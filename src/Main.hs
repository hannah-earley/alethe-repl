module Main where

import System.Environment (getArgs)
import System.Console.Haskeline

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import Control.Monad.State.Strict
import Control.Monad.Trans (lift)
import Control.Monad (void)

import Language
import Parser
import Compiler
import Miscellanea

--

data Env = Env { program  :: Program
               , sources  :: [FilePath]
               , bindings :: Map String Term
               } deriving (Show)

main :: IO ()
main = do files <- getArgs
          evalStateT (load files >> runInputT defaultSettings (withInterrupt loop))
                     Env { program = Program [], sources = [], bindings = M.empty }

type EnvIO = StateT Env IO

loop :: InputT EnvIO ()
loop = handleInterrupt loop $
       getInputReq >>= \case
         Left e     -> outputStrLn (show e) >> loop
         Right Quit -> outputStrLn "bye."
         Right z    -> lift (switch z) >> loop
  where getInputReq = maybe (Right Quit) id <$> fmap readInput <$> getInputLine "% "

switch :: Request -> EnvIO ()
switch Noop                 = return ()
switch Reload               = sources <$> get >>= load
switch (Load fs)            = load fs
switch (EvaluateOpen t)     = void $ goEval t
switch (EvaluateClosed t p) = goEval t >>= maybe (return ()) (goMatch p)
switch ShowVars             = get >>= liftIO . printVars . bindings
switch ShowProg             = get >>= liftIO . print . program
switch _                    = undefined

printVars :: Map String Term -> IO ()
printVars = putStr . showVars

goEval :: [Term] -> EnvIO (Maybe [Term])
goEval t = do progr <- program <$> get
              binds <- bindings <$> get
              case subAllDup binds t of
                Left vs -> liftIO $ do
                    putStrLn $ "Couldn't substitute the variable(s) "
                               ++ showMany ", " (Var <$> vs)
                    return Nothing
                Right t' ->
                  let x = evaluateRecLocal progr t'
                  in liftIO (print x) >> case x of
                    EvalSuccess t'' -> return $ Just t''
                    _               -> return $ Nothing

goMatch :: [Term] -> [Term] -> EnvIO ()
goMatch p t = do progr <- program <$> get
                 case unifyDup (isHalting progr) p t of
                   Nothing -> liftIO $ putStrLn "Couldn't unify resultant term."
                   Just vs -> liftIO (printVars vs) >> go vs
  where go binds' = modify $ \e -> e { bindings = binds' `M.union` bindings e }

load :: [FilePath] -> EnvIO ()
load files = do modify $ \e -> e { program = Program [], sources = files }
                liftIO (compile files) >>= \case
                    Left  e -> liftIO . putStrLn $ show e
                    Right p -> modify (\e -> e { program = p })