{-# LANGUAGE PackageImports, ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GeneralizedNewtypeDeriving,FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
-- A simple parser for the Frank language
module Parser where

import Control.Applicative
import Control.Monad
import Control.Monad.IO.Class

import Text.Trifecta
import "indentation-trifecta" Text.Trifecta.Indentation

import Data.Char
import qualified Data.Map.Strict as M

import Debug.Trace

import Text.Parser.Token as Tok
import Text.Parser.Token.Style
import qualified Text.Parser.Token.Highlight as Hi
import qualified Data.HashSet as HashSet

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, assertEqual, assertFailure, Assertion)

import Syntax
import qualified ExpectedTestOutput as ETO

newtype FrankParser t m a =
  FrankParser { runFrankParser :: IndentationParserT t m a }
  deriving (Functor, Alternative, Applicative, Monad, Parsing
           , IndentationParsing)

deriving instance (DeltaParsing m) => (CharParsing (FrankParser Char m))
deriving instance (DeltaParsing m) => (CharParsing (FrankParser Token m))
deriving instance (DeltaParsing m) => (TokenParsing (FrankParser Char m))

instance DeltaParsing m => TokenParsing (FrankParser Token m) where
  someSpace = FrankParser $ buildSomeSpaceParser someSpace haskellCommentStyle
  nesting = FrankParser . nesting . runFrankParser
  semi = FrankParser $ runFrankParser semi
  highlight h = FrankParser . highlight h . runFrankParser
  token p = (FrankParser $ token (runFrankParser p)) <* whiteSpace

type MonadicParsing m = (TokenParsing m, IndentationParsing m, Monad m)

frankStyle :: MonadicParsing m => IdentifierStyle m
frankStyle = IdentifierStyle {
    _styleName = "Frank"
  , _styleStart = satisfy (\c -> isAlpha c || c == '_')
  , _styleLetter = satisfy (\c -> isAlphaNum c || c == '_' || c == '\'')
  , _styleReserved = HashSet.fromList [ "data", "interface", "String", "Int"
                                      , "Char"]
  , _styleHighlight = Hi.Identifier
  , _styleReservedHighlight = Hi.ReservedIdentifier }

identifier :: MonadicParsing m => m String
identifier = Tok.ident frankStyle

reserved :: MonadicParsing m => String -> m ()
reserved = Tok.reserve frankStyle

prog :: (Applicative m, MonadicParsing m) => m (Prog Raw)
prog = MkProg <$ whiteSpace <*> many tterm

tterm :: MonadicParsing m => m (TopTm Raw)
tterm = MkDataTm <$> parseDataT <|>
        MkSigTm <$> try parseMHSig <|>
        MkClsTm <$> parseMHCls <|>
        MkItfTm <$> parseItf

parseDataT :: MonadicParsing m => m (DataT Raw)
parseDataT = do reserved "data"
                name <- identifier
                es <- many $ brackets $ parseEVar
                ps <- many identifier
                symbol "="
                xs <- localIndentation Gt ctrlist
                return $ MkDT name es ps xs

parseEVar :: MonadicParsing m => m Id
parseEVar = do mx <- optional identifier
               case mx of
                 Nothing -> return "£"
                 Just x -> return x

ctrlist :: MonadicParsing m => m [Ctr Raw]
ctrlist = sepBy parseCtr (symbol "|")

parseCtr :: MonadicParsing m => m (Ctr Raw)
parseCtr = do name <- identifier
              args <- many parseVType'
              return $ MkCtr name args

parseMHSig :: MonadicParsing m => m MHSig
parseMHSig = do name <- identifier
                symbol ":"
                ty <- parseCType
                return (MkSig name ty)

parseMHCls :: MonadicParsing m => m MHCls
parseMHCls = do name <- identifier
                ps <- choice [some parsePattern, symbol "!" >> return []]
                symbol "="
                seq <- localIndentation Gt parseRawTmSeq
                return $ MkMHCls name (MkCls ps seq)

parseItf :: MonadicParsing m => m (Itf Raw)
parseItf = do reserved "interface"
              name <- identifier
              ps <- many identifier
              symbol "="
              xs <- localIndentation Gt $ sepBy1 parseCmd (symbol "|")
              return (MkItf name ps xs)

parseCmd :: MonadicParsing m => m (Cmd Raw)
parseCmd = do cmd <- identifier
              symbol ":"
              (xs,y) <- parseCmdType
              return (MkCmd cmd xs y)

-- only value arguments and result type
parseCmdType :: MonadicParsing m => m ([VType Raw], VType Raw)
parseCmdType = do vs <- sepBy1 parseVType (symbol "->")
                  if length vs == 1 then return ([],head vs)
                  else return (init vs, last vs)

parseCType :: MonadicParsing m => m (CType Raw)
parseCType = do (ports, peg) <- parsePortsAndPeg
                return $ MkCType ports peg

parsePortsAndPeg :: MonadicParsing m => m ([Port Raw], Peg Raw)
parsePortsAndPeg = try (do port <- parsePort
                           symbol "->" -- Might fail; previous parse was peg.
                           (ports, peg) <- parsePortsAndPeg
                           return (port : ports, peg)) <|>
                       (do peg <- parsePeg
                           return ([], peg))

parsePort :: MonadicParsing m => m (Port Raw)
parsePort = do adj <- parseAdj
               ty <- parseVType
               return $ MkPort adj ty

parsePeg :: MonadicParsing m => m (Peg Raw)
parsePeg = do ab <- parseAb
              ty <- parseVType
              return $ MkPeg ab ty

parseAdj :: MonadicParsing m => m (Adj Raw)
parseAdj = do mxs <- optional $ angles (sepBy parseAdj' (symbol ","))
              case mxs of
                Nothing -> return $ MkAdj M.empty
                Just xs -> return $ MkAdj (M.fromList xs)

parseAdj' :: MonadicParsing m => m (Id, [VType Raw])
parseAdj' = do x <- identifier
               ts <- many parseVType
               return (x, ts)

parseDTAb :: MonadicParsing m => m (Ab Raw)
parseDTAb = do xs <- brackets (sepBy parseAb' (symbol ","))
               return $ MkAb (MkAbVar "£") (M.fromList xs)

parseAb :: MonadicParsing m => m (Ab Raw)
parseAb = do mxs <- optional $ brackets (sepBy parseAb' (symbol ","))
             case mxs of
               Nothing -> return $ MkAb (MkAbVar "£") M.empty
               Just xs -> return $ MkAb (MkAbVar "£") (M.fromList xs)

parseAb' :: MonadicParsing m => m (Id, [VType Raw])
parseAb' = do x <- identifier
              ts <- many parseVType
              return (x, ts)

parseVType :: MonadicParsing m => m (VType Raw)
parseVType = try parseDTType <|>
             parseVType'

parseVType' :: MonadicParsing m => m (VType Raw)
parseVType' = parens parseVType <|>
              MkSCTy <$> try (braces parseCType) <|>
              MkStringTy <$ reserved "String" <|>
              MkIntTy <$ reserved "Int" <|>
              MkCharTy <$ reserved "Char" <|>
              MkTVar <$> identifier

-- Parse a potential datatype. Note it may actually be a type variable.
parseDTType :: MonadicParsing m => m (VType Raw)
parseDTType = do x <- identifier
                 abs <- many parseDTAb
                 ps <- localIndentation Gt $ many parseVType'
                 return $ MkDTTy x abs ps

parseRawTmSeq :: MonadicParsing m => m (Tm Raw)
parseRawTmSeq = do tm1 <- parseRawTm
                   m <- optional $ symbol ";"
                   case m of
                     Just _ -> do tm2 <- parseRawTmSeq
                                  return $ MkTmSeq tm1 tm2
                     Nothing -> return tm1

parseRawTm :: MonadicParsing m => m (Tm Raw)
parseRawTm = try parseRawOpTm <|>
             parseRawTm'

parseRawOpTm :: MonadicParsing m => m (Tm Raw)
parseRawOpTm = do uminus <- optional $ symbol "-"
                  tm1 <- parseRawOperandTm
                  let tm1' = case uminus of
                        Just _ -> MkRawComb "-" [MkInt 0,tm1]
                        Nothing -> tm1
                  (do op <- choice $ map symbol ["+","-","*","/"]
                      tm2 <- parseRawOperandTm
                      return $ MkRawComb op [tm1', tm2]) <|> return tm1'

parseRawOperandTm :: MonadicParsing m => m (Tm Raw)
parseRawOperandTm = try parseComb <|>
                    parens parseRawOpTm <|>
                    try parseNullaryComb <|>
                    parseId <|>
                    MkInt <$> natural

parseId :: MonadicParsing m => m (Tm Raw)
parseId = do x <- identifier
             return $ MkRawId x

parseNullaryComb :: MonadicParsing m => m (Tm Raw)
parseNullaryComb = do x <- identifier
                      symbol "!"
                      return $ MkRawComb x []

parseRawTm' :: MonadicParsing m => m (Tm Raw)
parseRawTm' = parens parseRawTmSeq <|>
              try parseNullaryComb <|>
              parseId <|>
              MkSC <$> parseRawSComp <|>
              MkStr <$> stringLiteral <|>
              MkInt <$> natural <|>
              MkChar <$> charLiteral

parseComb :: MonadicParsing m => m (Tm Raw)
parseComb = do x <- identifier
               args <- choice [some parseRawTm', symbol "!" >> pure []]
               return $ MkRawComb x args

parseRawClause :: MonadicParsing m => m (Clause Raw)
parseRawClause = do ps <- choice [try parsePatterns, pure []]
                    seq <- parseRawTmSeq
                    return $ MkCls ps seq
  where parsePatterns =
          do ps <- sepBy1 (parseVPat >>= return . MkVPat) (symbol ",")
             symbol "->"
             return $ ps

parsePattern :: MonadicParsing m => m Pattern
parsePattern = try parseCPat <|> MkVPat <$> parseVPat

parseCPat :: MonadicParsing m => m Pattern
parseCPat = between (symbol "<") (symbol ">") $
            try parseCmdPat <|> parseThunkPat

parseThunkPat :: MonadicParsing m => m Pattern
parseThunkPat = do x <- identifier
                   return (MkThkPat x)

parseCmdPat :: MonadicParsing m => m Pattern
parseCmdPat = do cmd <- identifier
                 ps <- many parseVPat
                 symbol "->"
                 g <- identifier
                 return (MkCmdPat cmd ps g)

parseVPat :: MonadicParsing m => m ValuePat
parseVPat = parseDataTPat <|>
            (do x <- identifier
                return $ MkVarPat x) <|>
            MkIntPat <$> try integer <|> -- try block for unary minus
            MkCharPat <$> charLiteral <|>
            MkStrPat <$> stringLiteral

parseDataTPat :: MonadicParsing m => m ValuePat
parseDataTPat = parens $ do k <- identifier
                            ps <- many parseVPat
                            return $ MkDataPat k ps

parseRawSComp :: MonadicParsing m => m (SComp Raw)
parseRawSComp = localIndentation Gt $ absoluteIndentation $
                do cs <- braces $ sepBy parseRawClause (symbol "|")
                   return $ MkSComp cs

evalCharIndentationParserT :: Monad m => FrankParser Char m a ->
                              IndentationState -> m a
evalCharIndentationParserT = evalIndentationParserT . runFrankParser

evalTokenIndentationParserT :: Monad m => FrankParser Token m a ->
                               IndentationState -> m a
evalTokenIndentationParserT = evalIndentationParserT . runFrankParser

runParse ev p input
 = let indA = ev p $ mkIndentationState 0 infIndentation True Ge
   in case parseString indA mempty input of
    Failure err -> Left (show err)
    Success t -> Right t

runProgParse ev input = runParse ev prog input

runParseFromFileEx ev p fname =
  let indA = ev p $ mkIndentationState 0 infIndentation True Ge in
  do res <- parseFromFileEx indA fname
     case res of
       Failure err -> return $ Left (show err)
       Success t -> return $ Right t

runProgParseFromFileEx ev fname = runParseFromFileEx ev prog fname

--runCharParseFromFile = runParseFromFileEx evalCharIndentationParserT
runTokenParseFromFile = runProgParseFromFileEx evalTokenIndentationParserT

--runCharParse = runParse evalCharIndentationParserT
runTokenParse p = runParse evalTokenIndentationParserT p
runTokenProgParse = runProgParse evalTokenIndentationParserT

input = [ "tests/evalState.fk"
        , "tests/listMap.fk"
        , "tests/suspended_computations.fk"
        , "tests/fib.fk"
        , "tests/paper.fk"]

--outputc = map runCharParseFromFile input
outputt = map runTokenParseFromFile input

assertParsedOk :: (Show err, Show a, Eq a) => IO (Either err a) -> IO a
                  -> Assertion
assertParsedOk actual expected =
  do x <- actual
     case x of
       Right ok -> do y <- expected
                      assertEqual "parsing succeeded, but " y ok
       Left err -> do y <- expected
                      assertFailure ("parse failed with " ++ show err
                                     ++ ", expected " ++ show y)

allTests :: TestTree
allTests =
  testGroup "Frank (trifecta)"
  [
    -- TODO: Look into why adding comments have broken char parsing
    -- testGroup "char parsing" $
    -- map (uncurry testCase) $
    -- zip input $ map (uncurry assertParsedOk) (zip outputc ETO.expected),
    testGroup "token parsing" $
    map (uncurry testCase) $
    zip input $ map (uncurry assertParsedOk) (zip outputt ETO.expected)
  ]
