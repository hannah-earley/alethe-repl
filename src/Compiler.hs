module Compiler where

import Language
import Parser
import Miscellanea

import Data.Set (Set)
import qualified Data.Set as S
import qualified Data.Map.Strict as M
import Data.Vector ((!))
import qualified Data.Vector as V
import Control.Arrow ((***))
import Data.List (nub)
import Data.Maybe (catMaybes)
import Data.Either (partitionEithers)

compWith :: [Definition] -> [FilePath] -> IO (Either CompilationError Program)
compWith prel ps = loadPrograms ps >>= return . (compile' . (prel++) =<<)

compile :: [FilePath] -> IO (Either CompilationError Program)
compile = compWith prelude

compile0 :: [FilePath] -> IO (Either CompilationError Program)
compile0 = compWith []

compile' :: [Definition] -> Either CompilationError Program
compile' ds = fmap Program $ cVar ds >> cAmbi ds >> tgSolves (ds)

-- phase 1: variable conflict and context scope checks

cVar :: [Definition] -> Either CompilationError ()
cVar = handle . filter checkDef
  where
    poolCtxts (Terminus _) = []
    poolCtxts (Rule l r d) = l ++ r ++ map _decRule d
    checkCtxt = any (>1) . M.elems . vars'
    checkDef = any checkCtxt . poolCtxts
    handle [] = Right ()
    handle ds = Left $ VarConflictError ds

-- phase 2: ambiguity checks

-- best case O(n^2), worst O(n^3), average O(n^2)
cAmbi :: [Definition] -> Either CompilationError ()
cAmbi defs = handle . map (vdefs !) . nub . concatMap triangles $ terms ++ rules
  where vdefs = V.fromList defs
        (terms,rules) = partitionContexts defs
        handle [] = Right ()
        handle as = Left $ AmbiguityError as

        p (l,c) (l',c') = l /= l' && compatible c c'
        triangles (l,c) = case promisc $ filter (p (l,c)) rules of
                            [] -> []
                            ls -> l:ls

        promisc [] = []
        promisc ((l,c):xs) = case filter (compatible c . snd) xs of
                               [] -> promisc xs
                               ys -> (l : map fst ys) ++ promisc xs

partitionContexts :: [Definition] -> ([(Int,Context)],[(Int,Context)])
partitionContexts = (concat *** concat) . partitionEithers . zipWith f [0..]
  where f n (Terminus t) = Left [(n,Context (Var "") t)]
        f n (Rule lhs rhs _) = Right . map (n,) $ lhs ++ rhs


-- phase 3: resolving implementation paths
-- tg = transition graph

tgBuild :: [Declaration] -> [Set String] -> [(Set String, [(Either Int Int, Int, Set String)])]
tgBuild rules = build S.empty . S.fromList
  where
    transitions = concat $ zipWith mkTrans ([0..] :: [Int]) rules
    mkTrans n (Declaration w (Context c p))
      = [(Right n,w,cv,pv),(Left n,w,pv,cv)]
      where cv = vars c
            pv = vars p
    goTrans node (lab,wei,lvars,rvars)
      | (lvars `S.isSubsetOf` node) && (S.null $ rvars `S.intersection` node)
                  = Just (lab, wei, (node S.\\ lvars) `S.union` rvars)
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

tgSolve :: [l] -> Definition -> Maybe ([(l,l,Strategy)],[l])
tgSolve (x:y:zs) (Terminus t) = case asplit t of
    (l,r) | l == r    -> Just ([(x,x,StratHalt l)],(y:zs))
          | otherwise -> Just ([(x,y,StratHalt l), (y,x,StratHalt r)],zs)
tgSolve (x:y:zs) (Rule l r d) =
  do (_,pl1) <- dijkstra (M.fromList $ tgBuild d [nl,nr]) nl nr
     let pl2 = reverse $ map flipEither pl1
     return ([(x,y,Strategy l1 vc pl1 r1), (y,x,Strategy l2 vc pl2 r2)], zs)
  where (nl,l1,r2) = varsplit l
        (nr,l2,r1) = varsplit r
        vc = V.fromList $ map _decRule d
tgSolve _ _ = Nothing

tgSolves :: [Definition] -> Either CompilationError [(Int,Int,Strategy)]
tgSolves = mapLeft ReversibilityError . fmap concat . combineEithers . go [0..]
  where
    go _ []      = []
    go ns (d:ds) = case tgSolve ns d of
                     Nothing        -> Left d   : go ns  ds
                     Just (xs, ns') -> Right xs : go ns' ds