module Compiler where

import Language
import Parser
import Miscellanea

import Data.Set (Set)
import qualified Data.Set as S
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import Data.Vector ((!))
import qualified Data.Vector as V
import Control.Arrow ((***))
import Data.List (nub)
import Data.Maybe (catMaybes)
import Data.Either (partitionEithers)

compWith' :: [Definition] -> Either CompilationError [Definition] -> Either CompilationError Program
compWith' prel = (>>= compile') . fmap (prel++)

compWith :: [Definition] -> [FilePath] -> IO (Either CompilationError Program)
compWith prel = fmap (compWith' prel) . loadPrograms

compile :: [FilePath] -> IO (Either CompilationError Program)
compile = compWith prelude

compile0 :: [FilePath] -> IO (Either CompilationError Program)
compile0 = compWith []

compile' :: [Definition] -> Either CompilationError Program
compile' ds = fmap mkProg $ cVar ds >> cAmbi ds >> tgSolves (ds)

mkProg :: [(Int,Int,Strategy)] -> Program
mkProg xs = Program xs (searchIndexProg $ buildIndexProg xs)

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
cAmbi defs = handle . map (vdefs !) . nub . concatMap triangles $ halts ++ rules
  where vdefs = V.fromList defs
        (halts,rules) = partitionContexts defs
        handle [] = Right ()
        handle as = Left $ AmbiguityError as

        p (l,c) (l',c') = l /= l' && compatible c c'
        triangles (l,c) = case promisc $ filter (p (l,c)) rules of
                            [] -> []
                            ls -> l:ls
        -- above: first, filter rules for all which are compatible with (l,c),
        -- below: then see if any of _these_ rules are compatible with each
        --        other; if so, then we have found a triangle and can report
        --        it as an ambiguity
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
--
-- A transition graph has as nodes sets of variables (Set String), and its edges
-- are directed, are labelled by the sub-rule that maps between these sets of variables,
-- and are weighted by the cost annotation.
--
-- A sub-rule is a declaration c:p with context c and term pattern p; if these are
-- uniquely labelled by Ints, n, then Left n means the consumption of p_n and production
-- of c_n (i.e. instantiation of the sub-term) whilst Right n means the converse (i.e.
-- consumption of the sub-term).
--
-- tgBuild takes an ordered list of declarations, and some initial nodes (typically the
-- variable set for the left side of the main rule, and the set for the right side), and
-- constructs a term graph by transitively applying the declarations from the initial nodes,
-- walking as far as possible. Clearly we want to be able to get from the left node to the
-- right node, and if such a path does not exist then we will fail at the next step...
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
-- now we try to solve for paths from the left node to the right node (and vice-versa);
-- first we handle the trivially satisfied case of halting states,
tgSolve :: [l] -> Definition -> Maybe ([(l,l,Strategy)],[l])
tgSolve (x:y:zs) (Terminus t) = case asplit t of
    (l,r) | l == r    -> Just ([(x,x,StratHalt l)],(y:zs))
          | otherwise -> Just ([(x,y,StratHalt l), (y,x,StratHalt r)],zs)
-- then the interesting case of computational rules, in which we build the transition graph
-- and then apply dijkstra's algorithm to obtain a path of minimal cost between the left and
-- right nodes (nl and nr), or else fail
tgSolve (x:y:zs) (Rule l r d) =
  do (_,pl1) <- dijkstra (M.fromList $ tgBuild d [nl,nr]) nl nr
     let pl2 = reverse $ map flipEither pl1
     return ([(x,y,Strategy l1 vc pl1 r1), (y,x,Strategy l2 vc pl2 r2)], zs)
  where (nl,l1,r2) = varsplit l
        (nr,l2,r1) = varsplit r
        vc = V.fromList $ map _decRule d
tgSolve _ _ = Nothing
-- finally, solve for _all_ rules, and report which rules (if any) fail
tgSolves :: [Definition] -> Either CompilationError [(Int,Int,Strategy)]
tgSolves = mapLeft ReversibilityError . fmap concat . combineEithers . go [0..]
  where
    go _ []      = []
    go ns (d:ds) = case tgSolve ns d of
                     Nothing        -> Left d   : go ns  ds
                     Just (xs, ns') -> Right xs : go ns' ds

-- phase 4: fast pattern lookups by building a trie-like structure...

buildIndexProg :: [(Int,Int,Strategy)] -> IndexCtxt (Int,Int,Strategy)
buildIndexProg xs = buildIndexCtxt . catMaybes $ zipWith f xs xs
  where
    emp = Context (Var "")
    f (_,_,StratHalt ts)       s = Just (emp ts, s)
    f (_,_,Strategy [x] _ _ _) s = Just (x,      s)
    f _                        _ = Nothing
      -- we don't support multiparty rules yet, see the below comment
      -- for a sketch of what to do when we do...

searchIndexProg :: IndexCtxt (Int,Int,Strategy) -> [Context] -> [(Int,Int,Strategy)]
searchIndexProg idx [c] = searchIndexCtxt idx c
searchIndexProg _   _   = []

{- IndexCtxts is tricky as it needs to match a subset of the input in any order. I.e, if we search for a strategy consistent with a current set of terms [A,B,C,D], then we can match rules like [D,A,B], [C,B], etc but not [A,C,D,E] etc. We therefore map each input to a tuple (n,i,v); to be consistent, we must obtain (n,0,v), (n,1,v), ..., (n,n-1,v). We should then also indicate which terms in the input matched. -}
data IndexCtxts v = IndexCtxts (IndexCtxt (Int,Int,v)) deriving Show
buildIndexCtxts :: [([Context],v)] -> IndexCtxts v
buildIndexCtxts = error "not yet defined!"

data IndexCtxt v = IndexCtxt (IndexTerms v) deriving Show

data IndexTerm v = IndexTerm { _idxAtom :: Map Integer (Map String [v])
                             , _idxVar  :: [v]
                             , _idxIntl :: Map String [v]
                             , _idxComp :: IndexTerms v
                             } deriving (Show)

data IndexTerms v = IndexTerms (Map Int (IndexTerms' v)) deriving Show

data IndexTerms' v = IndexCar (IndexTerm (IndexTerms' v))
                   | IndexCdr [v]
                   deriving (Show)

buildIndexCtxt :: [(Context,v)] -> IndexCtxt v
buildIndexCtxt = IndexCtxt . buildIndexTerms . map (\(Context c x,v) -> (c:x,v))

searchIndexCtxt :: IndexCtxt v -> Context -> [v]
searchIndexCtxt (IndexCtxt idx) (Context c x) = searchIndexTerms idx (c:x)

buildIndexTerm :: [(Term,v)] -> IndexTerm v
buildIndexTerm ts = IndexTerm atIdx vaIdx inIdx coIdx
  where
    f g = catMaybes $ map g ts
    getAt (Atom n x,b)    = Just (n,(x,b)); getAt _ = Nothing; ats = f getAt
    getVa (Var v,b)       = Just (v    ,b); getVa _ = Nothing; vas = f getVa
    getCo (Compound xs,b) = Just (xs   ,b); getCo _ = Nothing; cos'= f getCo
    getIn (Internal_ x,b) = Just (x    ,b); getIn _ = Nothing; ins = f getIn
    -- getAs (Asymm l r,b)   = Just ((l,r),b); getAs _ = Nothing; ass = f getAs
    -- we shouldn't have any asymms to match against as these should be split in tgSolves

    atIdx = M.fromList . map (fmap $ M.fromList . multibag) $ multibag ats
    vaIdx = map snd vas
    inIdx = M.fromList $ multibag ins
    coIdx = buildIndexTerms cos'

searchIndexTerm :: IndexTerm v -> Term -> [v]
searchIndexTerm (IndexTerm a v _ _) (Atom n x) =
  v ++ maybe [] id (a M.!? n >>= (M.!? x))
searchIndexTerm (IndexTerm _ v i _) (Internal_ x) =
  v ++ maybe [] id (i M.!? x)
searchIndexTerm (IndexTerm _ v _ c) (Compound ts) =
  v ++ searchIndexTerms c ts
searchIndexTerm _ _ = error "searchIndexTerm: error! asymm or var found in concrete term."

buildIndexTerms :: [([Term],v)] -> IndexTerms v
buildIndexTerms ts = IndexTerms . M.fromList . map gogo
                                . multibag $ zip (map (length . fst) ts) ts
  where
    gogo (n,xs) = (n,go n xs)

    go 0 = IndexCdr . map snd
    go n = IndexCar . buildIndexTerm
                . map (fmap $ go (n-1))
                . multibag . map f

    f (x:xs, b) = (x,(xs,b))
    f _         = error "buildIndexTerms: internal error"

searchIndexTerms :: IndexTerms v -> [Term] -> [v]
searchIndexTerms (IndexTerms m) ts =
  maybe [] (flip searchIndexTerms' ts) $ m M.!? length ts

searchIndexTerms' :: IndexTerms' v -> [Term] -> [v]
searchIndexTerms' (IndexCdr vs) [] = vs
searchIndexTerms' (IndexCar idx) (t:ts) =
  concatMap (flip searchIndexTerms' ts) $ searchIndexTerm idx t
searchIndexTerms' _ _ = []