module Helper where

import Control.Monad (liftM2)
import Control.Applicative ((<$))
import System.FilePath.Posix (normalise, (</>))
import Data.List (intercalate)

if' :: Bool -> a -> a -> a
if' True  x _ = x
if' False _ y = y

($>) :: Functor f => f a -> b -> f b
($>) = flip (<$)
infixr 4 $>

(<//>) :: FilePath -> FilePath -> FilePath
path1 <//> path2 = normalise $ path1 </> path2
infixr 5 <//>

(|||) :: Monad m => m Bool -> m Bool -> m Bool
(|||) = liftM2 (||)
infixr 2 |||

showMany :: Show a => String -> [a] -> String
showMany sep = intercalate sep . map show
showSp = showMany " "
showSemi = showMany "; "
