{-# LANGUAGE GADTs #-}
module Main where

import Parser
import Compile
import TypeCheck
import Syntax
import RefineSyntax
import DesugarSyntax
import Debug

import qualified Shonky.Semantics as Shonky

import Control.Monad

import Data.IORef
import qualified Data.Map.Strict as M
import Data.List
import Data.Maybe (fromMaybe)

import System.Console.CmdArgs.Explicit
import System.Directory
import System.Environment
import System.Exit
import System.IO

import Text.Read (readMaybe)

import Debug.Trace (trace)

type Args = [(String,[String])]

type PMap = M.Map FilePath (Prog Raw)

-- Function checks whether or not a main function exists in the program
existsMain :: Prog t -> Bool
existsMain (MkProg xs) = any (== "main") [id | DefTm (Def id _ _ _) _ <- xs]

splice :: Prog Raw -> Tm Raw -> Prog Raw
splice (MkProg xs) tm = MkProg $ xs ++ ys
  where ys = [sig, cls]
        sig = SigTm (Sig id (CType [] peg b) b) b
        peg = Peg ab ty b
        ty = TVar "%X" b
        ab = Ab (AbVar "£" b) (ItfMap M.empty (Raw Generated)) b
        cls = ClsTm (MHCls id (Cls [] tm b) b) b
        id = "%eval"
        b = Raw Generated

--TODO: LC: Fix locations?
exorcise :: Prog Desugared -> (Prog Desugared, TopTm Desugared)
exorcise (MkProg xs) = (prog, DefTm (head evalDef) a)
  where prog = MkProg (map (swap DataTm a) dts ++
                       map (swap ItfTm a) itfs ++
                       map (swap DefTm a) hdrs)
        dts = [d | DataTm d _ <- xs]
        itfs = [i | ItfTm i _ <- xs]
        defs = [d | DefTm d _ <- xs]
        (evalDef,hdrs) = partition isEvalTm defs
        isEvalTm (Def id _ _ _) = id == "%eval"
        a = Desugared Generated

extractEvalUse :: TopTm Desugared -> Use Desugared
extractEvalUse (DefTm (Def _ _ [cls] _) _) = getBody cls
  where getBody (Cls [] (Use u _) _) = u
        getBody _ = error "extractEvalUse: eval body invariant broken"

glue :: Prog Desugared -> TopTm Desugared -> Prog Desugared
glue (MkProg xs) x = MkProg (x : xs)

parseYTLine :: String -> Maybe Int
parseYTLine st
  | take 7 st == "--! YT=" = readMaybe (drop 7 st)
  | otherwise = Nothing

default_thresh :: Int
default_thresh = 4000

parseYT :: FilePath -> IO Int
parseYT fileName =
  do mint <- (parseYTLine . head . lines) <$> readFile fileName
     return (fromMaybe default_thresh mint)

parseProg :: FilePath -> Args -> IO (Either String (Prog Raw))
parseProg fileName args =
  do m <- pProg (Right M.empty) fileName
     case m of
       Left msg  -> return $ Left msg
       Right map -> return $ Right $ MkProg $ M.foldl combine [] map
  where pProg :: Either String PMap -> FilePath -> IO (Either String PMap)
        pProg (Left msg) _ = return $ Left msg
        pProg (Right map) fname | M.member fname map = return $ Right map
        pProg (Right map) fname =
          let ext = if isSuffixOf ".fk" fname then "" else ".fk" in
          do m <- parseFile (fname ++ ext) incPaths
             case m of
               Left msg -> return $ Left msg
               Right (p,fs) -> foldM pProg (Right (M.insert fname p map)) fs

        combine :: [TopTm Raw] -> Prog Raw -> [TopTm Raw]
        combine xs (MkProg ys) = xs ++ ys

        incPaths :: [String]
        incPaths = case lookup "inc" args of
          Just xs -> xs
          Nothing -> []

        parseFile :: String -> [FilePath] ->
                     IO (Either String (Prog Raw,[String]))
        parseFile name incs = let fs = name : map (++ name) incs in
          do m <- foldM g Nothing fs
             case m of
               Nothing ->
                 die ("could not find " ++ name ++
                      " in search path:" ++ (concat $ intersperse "," fs))
               Just x -> runTokenProgParse <$> readFile x
          where g :: Maybe FilePath -> FilePath -> IO (Maybe FilePath)
                g Nothing x = do b <- doesFileExist x
                                 return $ if b then Just x else Nothing
                g x@(Just _) _ = return x

parseEvalTm :: String -> IO (Tm Raw)
parseEvalTm v = case runTokenParse tm v of
  Left err -> die err
  Right tm -> return tm

refineComb :: Either String (Prog Raw) -> Tm Raw -> IO (Prog Refined)
refineComb prog tm = case prog of
    Left err -> die err
    Right p -> case refine (splice p tm) of
      Left err -> die err
      Right p' -> return p'

refineAndDesugarProg :: Either String (Prog Raw) -> IO (Prog Desugared)
refineAndDesugarProg p =
  case p of
    Left err -> die err
    Right p -> case refine p of
      Left err -> die err
      Right p' -> return $ desugar p'

checkProg :: Prog Desugared -> Args -> IO (Prog Desugared)
checkProg p _ =
  case check p of
    Left err -> die err
    Right p' -> return p'

checkUse :: Prog Desugared -> Use Desugared -> IO (Use Desugared, VType Desugared)
checkUse p use =
  case inferEvalUse p use of
    Left err -> die err
    Right (use, ty) -> return (use, ty)

compileProg :: String -> Prog Desugared -> Args -> IO Shonky.Env
compileProg progName p args =
  if ("output-shonky",[]) `elem` args then
    do compileToFile p progName
       Shonky.loadFile progName
  else return $ Shonky.load $ compile p

-- This is where any commands to be handled 'outside' of Frank get handled.
evalProg :: Int -> Shonky.Env -> String -> IO ()
evalProg thresh env tm =
  case Shonky.try thresh env tm of
    (Shonky.Ret v, _) -> putStrLn $ (show . Shonky.ppVal) v
    -- returning operation call and count so far
    (comp, k) -> do -- putStrLn $ "Generated computation: " ++ show comp
               -- carry on running, with count thus far
               v <- Shonky.ioHandler (comp, k)
               putStrLn $ (show . Shonky.ppVal) v


compileAndRunProg :: String -> Args -> IO ()
compileAndRunProg fileName args =
  do let progName = takeWhile (/= '.') fileName
     -- Here we need to look at the file to see if it's got a yielder in there
     prog <- parseProg fileName args
     yieldThresh <- parseYT fileName
     case lookup "eval" args of
       Just [v] -> do tm <- parseEvalTm v
                      -- lift tm to top term and append to prog
                      p <- refineComb prog tm
                      -- tear apart again
                      let (p',ttm) = exorcise (desugar p)
                          use = extractEvalUse ttm
                      p'' <- checkProg p' args
                      (use', _) <- checkUse p'' use
                      env <- compileProg progName (glue p'' ttm) args
                      evalProg yieldThresh env "%eval()"
       Just _ -> die "only one evaluation point permitted"
       Nothing -> do p <- refineAndDesugarProg prog
                     p' <- checkProg p args
                     env <- compileProg progName p' args
                     case lookup "entry-point" args of
                       Just [v] -> evalProg yieldThresh env (v ++ "()")
                       Just _  -> die "only one entry point permitted"
                       Nothing ->
                         if existsMain p' then
                           evalProg yieldThresh env "main()"
                         else
                           putStrLn ("Compilation successful! " ++
                                     "(no main function defined)")
arguments :: Mode Args
arguments =
  mode "frank" [] "Frank program" (flagArg (upd "file") "FILE")
  [flagNone ["output-shonky"] (("output-shonky",[]):)
   "Output Shonky code"
  ,flagNone ["debug-output"] (("debug-output",[]):)
   "Enable all debugging facilities"
  ,flagNone ["debug-verbose"] (("debug-verbose",[]):)
   "Enable verbose variable names etc. on output"
  ,flagNone ["debug-parser"] (("debug-parser",[]):)
    "Enable output of parser logs"
  ,flagNone ["debug-tc"] (("debug-tc",[]):)
   "Enable output of type-checking logs"
  ,flagReq ["include", "I"] updInc "INC"
   "Add a search path for source files"
  ,flagReq ["eval"] (upd "eval") "USE"
   "Run Frank computation USE (default: main!)"
  ,flagReq ["entry-point"] (upd "entry-point") "NAME"
   "Run computation NAME (default: main)"
  ,flagHelpSimple (("help",[]):)]
  where upd msg x v = Right $ (msg,[x]):v
        updInc x args = case lookup "inc" args of
          Just xs -> Right $ ("inc",x:xs):args
          Nothing -> Right $ ("inc",[x]):args

-- handy for testing in ghci
run f = compileAndRunProg f []

main :: IO ()
main = do
  hSetBuffering stdin NoBuffering
  hSetEcho stdin False
  args <- processArgs arguments
  let debugVerboseOn =   ("debug-output",[]) `elem` args ||
                         ("debug-verbose", []) `elem` args
      debugParserOn =    ("debug-output",[]) `elem` args ||
                         ("debug-parser", []) `elem` args
      debugTypeCheckOn = ("debug-output",[]) `elem` args ||
                         ("debug-tc", []) `elem` args
  writeIORef debugMode (debugVerboseOn, debugParserOn, debugTypeCheckOn)
  if ("help",[]) `elem` args then
     print $ helpText [] HelpFormatDefault arguments
  else case lookup "file" args of
    Just [f] -> compileAndRunProg f args
    Just _  -> die "too many Frank sources specified."
    Nothing -> die "no Frank source specified."
