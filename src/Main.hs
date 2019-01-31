module Main where

import Language
import Parser
import Compiler

test x = do Right prog <- compile ["kap/test.k"]
            let Right cs = readInput x
            return $ map (match prog . _decRule) cs

main :: IO ()
main = putStrLn "Hello, Haskell!"
