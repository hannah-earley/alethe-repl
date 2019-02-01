module Helper where

import Control.Monad (liftM2)
import Control.Applicative ((<$))
import System.FilePath.Posix (normalise, (</>))
import Data.List (intercalate)

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

list1 :: (a -> b) -> ([a] -> b) -> [a] -> b
list1 f _ [x] = f x
list1 _ g xs  = g xs

split :: [a] -> ([a],[a])
split (x:y:zs) = let ~(xs,ys) = split zs in (x:xs,y:ys)
split [x] = ([x],[])
split [] = ([],[])