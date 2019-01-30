module Compiler where

import Language
import Parser

import Data.Vector (Vector,(!))
import qualified Data.Vector as V
import Data.Graph (Graph)
import qualified Data.Graph as G
import qualified Data.Array.ST as A
import qualified Data.Array as Ar
import Control.Monad.ST (runST,ST)
import Control.Exception (assert)
import Control.Monad (filterM)
import qualified Data.Ix as I
import Data.List (nub)

compFiles ps = loadPrograms ps >>= return . (compile =<<)

-- compile :: [Definition] -> Either KappaError ()
compile ds = cAmbi ds >>= return



-- phase 1: ambiguity checks

cAmbi :: [Definition] -> Either KappaError (Vector Definition, Vector (Int,Context))
cAmbi ds = handle . map resolve $ runST $ pugBuild ctxts >>= pugAmbiguities
  where
    defs = V.fromList ds
    ctxts = V.fromList $ getContexts ds
    resolve = (defs!) . fst . (ctxts!)
    handle [] = Right (defs,ctxts)
    handle as = Left $ AmbiguityError as

getContexts :: [Definition] -> [(Int,Context)]
getContexts = concat . zipWith f [0..]
  where f n def@(Rule {}) = map (n,) $ lhs def ++ rhs def
        f n def@(Terminus t) = [(n,Context (Var "") t)]

pugBuild :: Vector (Int, Context) -> ST s (A.STArray s (Int,Int) Bool)
pugBuild ctxts =
    do arr <- A.newArray ((0,0),(n,n)) False
       sequence_ $ do 
          x <- range 0       n
          y <- range (x + 1) n
          let e = compatiblec (get x) (get y)
              w = A.writeArray arr
          return $ w (x,y) e >> w (y,x) e
       return arr
  where
    n = V.length ctxts - 1
    get = snd . (ctxts !)

range = curry I.range

pugAmbiguities :: A.STArray s (Int,Int) Bool -> ST s [Int]
pugAmbiguities arr =
    do ((0,0),(m,n)) <- A.getBounds arr
       assert (m == n) $ return ()
       prune n >> vertices n
  where
    edges i n = filterM (A.readArray arr) $ range (i,0) (i,n)
    pruneEdge [(i,j)] = w2 (i,j) False >> return True
    pruneEdge _       = return False
    pruneEdges n = any id <$> sequence [edges i n >>= pruneEdge | i <- range 0 n]
    prune n = do b <- pruneEdges n
                 if b then prune n
                      else return ()
    vertices n = nub . map snd . concat <$> mapM (flip edges n) (range 0 n)
    w = A.writeArray arr
    w2 (i,j) v = w (i,j) v >> w (j,i) v

