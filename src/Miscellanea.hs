module Miscellanea where

import Control.Monad (liftM2,guard)
import Control.Applicative ((<$))
import System.FilePath.Posix (normalise, (</>))
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import Data.Heap (Entry(..))
import qualified Data.Heap as H
import Data.List (nub,intercalate)
import Data.Either (partitionEithers)

data Extended a = NegInfinite | Finite a | PosInfinite
                deriving (Eq, Ord, Show)

instance (Ord a, Num a) => Num (Extended a) where
    PosInfinite + NegInfinite = error "PosInfinite + NegInfinite is undefined"
    PosInfinite + _ = PosInfinite
    NegInfinite + _ = NegInfinite
    Finite x + Finite y = Finite (x + y)
    Finite x + y = y + Finite x

    PosInfinite * x | x < 0     = NegInfinite
                    | x > 0     = PosInfinite
                    | otherwise = error "PosInfinite * (Finite x) is undefined"
    NegInfinite * x = PosInfinite * negate x
    Finite x * Finite y = Finite (x * y)
    Finite x * y = y * Finite x

    abs PosInfinite = PosInfinite
    abs NegInfinite = PosInfinite
    abs (Finite x) = Finite (abs x)

    signum PosInfinite = 1
    signum NegInfinite = -1
    signum (Finite x) = Finite (signum x)

    fromInteger = Finite . fromInteger

    negate PosInfinite = NegInfinite
    negate NegInfinite = PosInfinite
    negate (Finite x) = Finite (negate x)

dijkstra :: (Ord v, Ord w, Num w) => Map v [(l,w,v)] -> v -> v -> Maybe (w, [l])
dijkstra alist u v = summarise <$> (trace v . M.fromList $ dijkstra' alist u)
  where trace x m | x == u    = Just []
                  | otherwise = m M.!? x >>= \(l,w,p) -> ((w,l) :) <$> trace p m
        summarise []         = (0, [])
        summarise ((w,l):xs) = (w, reverse $ l : map snd xs)

dijkstra' :: (Ord v, Ord w, Num w) => Map v [(l,w,v)] -> v -> [(v,(l,w,v))]
dijkstra' alist u = go' 0 u queue
  where
    queue = H.fromList $ map (Entry PosInfinite . (,Nothing)) vertices
    vertices = nub . filter (/= u) . concatMap getVerts $ M.toList alist
    getVerts (x,ys) = x : map (\(_,_,xs) -> xs) ys

    go q = case H.uncons q of
            Just (Entry (Finite dist) (node, Just (l,prev)), q') ->
                (node,(l,dist,prev)) : go' dist node q'
            _ -> []

    go' d0 node = go . H.map update
      where
        neighbours = M.fromList $ maybe [] (map $ \(l,w,n) -> (n,(w,l))) (alist M.!? node)
        update e@(Entry d (x,_)) = case neighbours M.!? x of
            Just (w,l) -> let d' = Finite (d0 + w) in
                          if d' < d then Entry d' (x,Just (l,node)) else e
            Nothing -> e 

flipEither :: Either a b -> Either b a
flipEither (Left x)  = Right x
flipEither (Right y) = Left y

forceEither :: Show a => Either a b -> b
forceEither (Left e)  = error $ "forceEither: " ++ show e
forceEither (Right x) = x

combineEithers :: [Either a b] -> Either [a] [b]
combineEithers = go . partitionEithers
  where go ([],xs) = Right xs
        go (es,_)  = Left es

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f (Left x)  = Left (f x)
mapLeft _ (Right y) = Right y

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

mapMergeDisjoint :: Ord k => Map k v -> Map k v -> Maybe (Map k v)
mapMergeDisjoint m n = M.foldrWithKey go (Just m) n
  where go k v = (liftM2 (>>) (guard . not . M.member k) (return . M.insert k v) =<<)