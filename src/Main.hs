module Main where

import Language
import Parser
import Compiler

test x = do Right prog <- compile ["kap/test.k"]
            let Right cs = readInput x
            return $ map (match prog . pure) cs

test2 x = do Right prog <- compile ["kap/test.k"]
             let Right (c:_) = readInput x
             print c
             return $ evaluateRec prog [c]


main :: IO ()
main = putStrLn "Hello, Haskell!"
