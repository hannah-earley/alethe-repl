module Compiler where

import Language
import Parser
import Miscellanea

import Data.Set (Set)
import qualified Data.Set as S
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import Data.Vector (Vector,(!))
import qualified Data.Vector as V
import qualified Data.Array.ST as A
import qualified Data.Array as Ar
import Control.Monad.ST (runST,ST)
import Control.Exception (assert)
import Control.Monad (filterM)
import qualified Data.Ix as I
import Data.List (nub)
import Data.Maybe (catMaybes)

import Debug.Trace (trace)

data Strategy = StratStop [Term]
              | Strategy { lpatt :: [Context]
                         , rules :: Vector Context
                         , plan  :: [Either Int Int]
                         , rpatt :: [Context] }
              deriving (Show)

compFiles :: [FilePath] -> IO (Either KappaError [Strategy])
compFiles ps = loadPrograms ps >>= return . (compile =<<)

compile :: [Definition] -> Either KappaError [Strategy]
compile ds = cAmbi ds >> tgSolves ds

compTest ps = do Right defs <- loadPrograms ps
                 return defs

-- phase 1: ambiguity checks
-- pug = pattern unifying graph

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
          let e = compatible (get x) (get y)
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

-- phase 2: resolving implementation paths
-- tg = transition graph

tgBuild :: [Declaration] -> [Set String] -> [(Set String, [(Either Int Int, Int, Set String)])]
tgBuild rules = build S.empty . S.fromList
  where
    transitions = concat $ zipWith mkTrans [0..] rules
    mkTrans n (Declaration w (Context c p))
      = [(Right n,w,cv,pv),(Left n,w,pv,cv)]
      where cv = vars c
            pv = vars p
    goTrans node (lab,weight,lhs,rhs)
      | (lhs `S.isSubsetOf` node) && not (rhs `S.isSubsetOf` node)
                  = Just (lab, weight, (node S.\\ lhs) `S.union` rhs)
      | otherwise = Nothing

    walk node = catMaybes $ map (goTrans node) transitions
    es2ns = S.fromList . map (\(_,_,x) -> x)
    build visited from
      | S.null from = []
      | otherwise   = assocs ++ assocs'
      where
        assocs = map (\n -> (n,walk n)) $ S.elems from
        next = S.unions (map (es2ns . snd) assocs) S.\\ visited
        assocs' = build (visited `S.union` from) next

tgSolve :: Definition -> Either KappaError [Strategy]
tgSolve = mapLeft (CompilationError . pure) . tgSolve'

tgSolve' :: Definition -> Either Definition [Strategy]
tgSolve'   (Terminus t) = let (l,r) = asplit t in Right $ StratStop <$> nub [l,r]
tgSolve' x@(Rule l r d) = 
    do pl1 <- maybe (Left x) (Right . snd) mpl
       let pl2 = reverse $ map flipEither pl1
       return [Strategy l1 vc pl1 r1, Strategy l2 vc pl2 r2]
  where (nl,l1,r2) = varsplit l
        (nr,l2,r1) = varsplit r
        vc = V.fromList . flip map d $ \(Declaration _ c) -> c
        mpl = dijkstra (M.fromList $ tgBuild d [nl,nr]) nl nr

tgSolves :: [Definition] -> Either KappaError [Strategy]
tgSolves = mapLeft CompilationError . fmap concat . combineEithers . map tgSolve'
