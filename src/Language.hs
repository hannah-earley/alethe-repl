{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE FlexibleInstances #-}

module Language where

import Data.Set (Set)
import qualified Data.Set as S
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import Data.Vector (Vector,(!))
import Data.Char
import Data.Maybe (catMaybes)
import Data.List (intercalate,partition)
import Control.Monad (liftM2, foldM, guard)
import qualified Text.Parsec.Error as PE
import qualified Text.RawString.QQ as QQ

import Debug.Trace (trace)

import Miscellanea

-- prelude

prelude' :: String
prelude' = [QQ.r|

    !;
    data ();
    data Z;
    data S x;
    data Nil;
    data Cons car cdr;
    data Plus;
    data Minus;

|]

-- main interface

data Term = Atom     Integer String
          | Var      String
          | Asymm    Term Term
          | Compound [Term]
          deriving (Eq,Ord)

data Definition = Terminus [Term]
                | Rule { _defLPatt :: [Context]
                       , _defRPatt :: [Context]
                       , _defRules :: [Declaration] }

data Declaration = Declaration { _decWeight :: Int
                               , _decRule   :: Context }

data Context = Context { _cOHC  :: Term
                       , _cTerm :: [Term]}

-- display, sugar, properties, etc

instance Show Term where
    show (Atom n a)   = showAtom n a
    show (Var v)      = v
    show (Asymm l r)  = "(" ++ show l ++ " ! " ++ show r ++ ")"
    show (Compound t) = showComp t

instance Show Definition where
    show (Terminus t)         = "! " ++ showSp t ++ ";"
    show (Rule lhs rhs rules) = showRuleHead lhs rhs ++ showRules show rules

showRuleHead lhs rhs = case ruleInfixP lhs rhs of
                         Just (lhs',op,rhs') ->
                            showSp lhs' ++ " " ++ showInfix op ++ " " ++ showSp rhs'
                         Nothing -> showRuleHead' lhs rhs
showRuleHead' [Context c1@(Var ('|':_)) lp] [Context c2 rp]
    | c1 == c2 = showSp lp ++ " = " ++ showSp rp
showRuleHead' lhs rhs = showCtxts lhs ++ " = " ++ showCtxts rhs

ruleInfixP :: [Context] -> [Context] -> Maybe ([Term], Term, [Term])
ruleInfixP [Context c1@(Var ('|':_)) (op:lhs@(_:_))] [Context c2 (tt:rhs@(_:_))]
  | c1 == c2 && op == last rhs && last lhs == termTerm && tt == termTerm
              = Just (init lhs, op, init rhs)
ruleInfixP _ _ = Nothing

showInfix :: Term -> String
showInfix (Compound t) = "`" ++ showSp t ++ "`"
showInfix (Atom 0 a) | validOp a = a
showInfix (Atom n a) | validOp a = "~" ++ show n ++ ":" ++ a
showInfix (Atom n []) = "~" ++ show n ++ ":"
showInfix t = "`" ++ show t ++ "`"

showCtxts [c] = show c
showCtxts cs = "{ " ++ showSemi cs ++ " }"

showRules _ [] = ";"
showRules f xs = ":" ++ concatMap (("\n    " ++) . f) xs

showAtom' a = if invalidAtom a then "#" ++ show a else a
showAtom n a | at == atomZero = "0"
             | at == atomNil  = "[]"
             where at = Atom n a
showAtom 0 a = showAtom' a
showAtom n a = "#~" ++ show n ++ ":" ++ if invalidAtom a then show a else a

showComp t = let c = Compound t in
             case catMaybes [garbage' t, show <$> nat' c, show <$> str' c, sexpr' c] of
               (x:_) -> x
               []    -> "(" ++ showSp t ++ ")"

instance Show Declaration where
    show (Declaration w r) = show r ++ replicate w '.'

instance Show Context where
    show (Context c p) = show c ++ "| " ++ showSp p

nonVisible       = isControl        ||| isSpace  ||| isSeparator
reservedIdLetter = nonVisible       ||| (`elem` ".:;`#|!$~@()[]{}\"")
reservedIdStart  = reservedIdLetter ||| isDigit
reservedOpStart  = reservedIdStart  ||| isLetter ||| (`elem` "'_")

invalidAtom (x:xs) = isLower x || reservedIdStart x || any reservedIdLetter xs
invalidAtom [] = False

validOp a@(x:_) = not (invalidAtom a) && not (reservedOpStart x)
validOp []      = False

resolveAtomVar name@(x:_)
  | isLower x || x `elem` "_" = Var name
resolveAtomVar name           = atom name

atom = Atom 0
term0 = Compound []
termTerm = Compound []
term1 = list1 id Compound
phony = Atom (-999999999)

atomZero = atom "Z"
atomSucc = atom "S"
atomNil = atom "Nil"
atomCons = atom "Cons"
atomDup = atom "Dup"
atomPlus = atom "Plus"
atomMinus = atom "Minus"
atomGarbage = atom "Garbage"
atomChar c = atom ['\'', c]

nats = iterate (\n -> Compound [atomSucc, n]) atomZero
nat = (nats!!) . fromIntegral
cons car cdr = Compound [atomCons, car, cdr]
sexpr = flip $ foldr cons
slist = foldr cons atomNil
str = slist . map atomChar

garbage' (x:_) | x == atomGarbage = Just "{~GARBAGE~}"
garbage' _                        = Nothing

nat' (Compound [x,y]) | x == atomSucc = (1+) <$> nat' y
nat' a                | a == atomZero = Just (0 :: Integer)
nat' _                                = Nothing

str' (Compound [x, Atom 0 ['\'', c], cs]) | x == atomCons = (c:) <$> str' cs
str' a                                    | a == atomNil  = Just ""
str' _                                                    = Nothing

sexpr' t@(Compound [x, _, _]) | x == atomCons = Just $ "[" ++ intercalate " " (sexpr'' t) ++ "]"
sexpr' _                                      = Nothing
sexpr'' (Compound [x, car, cdr]) | x == atomCons = show car : sexpr'' cdr
sexpr'' a                        | a == atomNil  = []
sexpr'' e                                        = [".", show e]

-- term manipulation

termLeft :: Term -> Term
termLeft (Asymm l _) = l
termLeft (Compound t) = Compound $ map termLeft t
termLeft x = x

termRight :: Term -> Term
termRight (Asymm l _) = l
termRight (Compound t) = Compound $ map termRight t
termRight x = x

class Kappa a where
    asplit :: a -> (a,a)

    vars' :: a -> Map String Int
    vars :: a -> Set String
    vars = M.keysSet . vars'

    -- unify takes an extra argument that indicates whether a given subterm
    -- (that is explicitly pattern matched on) is in a legal state; this is
    -- mainly used to check whether each deconstructed term is in a halting state
    unify :: ([Term] -> Bool) -> a -> a -> Maybe (Map String Term)
    unify' :: a -> a -> Maybe (Map String Term)
    unify' = unify (const True)
    unifyDup :: ([Term] -> Bool) -> a -> a -> Maybe (Map String Term)

    -- sub only replaces variables which have a replacement,
    -- otherwise those vars are left intact; subAll insists
    -- on replacing *every* variable, and return Nothing otherwise.
    -- replacements are removed from the map as we go;
    -- both sub and subAll only allow each variable to be replaced
    -- once, but subAllDup allows for multiple occurences
    sub :: Map String Term -> a -> (Map String Term, a)
    subAll :: Map String Term -> a -> Maybe (Map String Term, a)
    subAllDup :: Map String Term -> a -> Either [String] a
    subAllRun :: Program -> Map String Term -> a
                         -> EvalStack' [Context] (Map String Term, a)
    evaluate :: Program -> [a] -> EvalStack' [Context] [a]

    compatible :: a -> a -> Bool

-- =

subAllRun1 :: Kappa a => Program -> Map String Term -> [a]
                                 -> EvalStack' [Context] (Map String Term, [a])
subAllRun1 _    m []     = do return (m, [])
subAllRun1 prog m (x:xs) = do (m', x')  <- subAllRun  prog m  x
                              (m'',xs') <- subAllRun1 prog m' xs
                              return (m'', x':xs')

showVars :: Map String Term -> String
showVars = concatMap go . M.toList
  where go (v,x) = "  " ++ v ++ " -> " ++ show x ++ "\n"

varsplit :: Kappa a => a -> (Set String, a, a)
varsplit t = let (l,r) = asplit t in (vars t, l, r)

zipStrict :: [a] -> [b] -> Maybe [(a,b)]
zipStrict []     []     = Just []
zipStrict (x:xs) (y:ys) = (:) (x,y) <$> zipStrict xs ys
zipStrict _      _      = Nothing

instance (Show a, Kappa a) => Kappa [a] where
    asplit = unzip . map asplit

    vars' = M.unionsWith (+) . map vars'
    vars = S.unions . map vars

    unify p patts terms = zipStrict patts terms >>= foldM go M.empty
      where go m (patt,term) = unify p patt term >>= mapMergeDisjoint m

    unifyDup p patts terms = zipStrict patts terms >>= foldM go M.empty
      where go m (patt,term) = unify p patt term >>= mapMergeEq m

    sub m []     = (m,[])
    sub m (x:xs) = let (m',x')   = sub m x
                       (m'',xs') = sub m' xs
                   in (m'',x':xs')

    subAll m [] = Just (m,[])
    subAll m (x:xs) = do (m',x')   <- subAll m x
                         (m'',xs') <- subAll m' xs
                         return (m'', x':xs')

    subAllDup m = mapLeft concat . combineEithers . map (subAllDup m)

    subAllRun prog m xs = do (m',xs') <- subAllRun1 prog m xs
                             xs''     <- evaluate prog xs'
                             return (m', xs'')

    evaluate = mapM . evaluate

    compatible xs ys = maybe False (all $ uncurry compatible) $ zipStrict xs ys

instance Kappa Term where
    asplit = liftM2 (,) termLeft termRight

    vars' (Atom _ _)  = M.empty
    vars' (Var v)     = M.singleton v 1
    vars' (Asymm l r) = M.unionWith  max (vars' l) (vars' r)
    vars' (Compound t)= vars' t

    vars (Atom _ _)  = S.empty
    vars (Var v)     = S.singleton v
    vars (Asymm l r) = S.union (vars l) (vars r)
    vars (Compound t)= vars t

    unify _ a@(Atom _ _) b@(Atom _ _) = guard (a == b) $> M.empty
    unify _ (Var v)      t            = return $ M.singleton v t
    unify p (Compound s) (Compound t) = guard (p t) >> unify p s t
    unify _ _            _            = Nothing

    unifyDup _ a@(Atom _ _) b@(Atom _ _) = guard (a == b) $> M.empty
    unifyDup _ (Var v)      t            = return $ M.singleton v t
    unifyDup p (Compound s) (Compound t) = guard (p t) >> unifyDup p s t
    unifyDup _ _            _            = Nothing

    sub m a@(Atom _ _) = (m,a)
    sub m (Var v)      = case m M.!? v of
                           Just x  -> (M.delete v m, x)
                           Nothing -> (m, Var v)
    sub m (Asymm l r)  = let (m1,l') = sub m l
                             (m2,r') = sub m r
                         in (m1 `M.union` m2, Asymm l' r')
    sub m (Compound t) = Compound <$> sub m t

    subAll m a@(Atom _ _) = Just (m,a)
    subAll m (Var v)      = (M.delete v m,) <$> m M.!? v
    subAll _ (Asymm _ _)  = Nothing -- asymm's have no right being here!
    subAll m (Compound t) = fmap Compound <$> subAll m t

    subAllDup _ a@(Atom _ _) = return a
    subAllDup m (Var v)      = maybe (Left [v]) return $ m M.!? v
    subAllDup _ (Asymm _ _)  = Left []
    subAllDup m (Compound t) = Compound <$> subAllDup m t

    subAllRun _    m a@(Atom _ _) = return (m,a)
    subAllRun _    m (Var v)      = case m M.!? v of
                                      Just t  -> return (M.delete v m, t)
                                      Nothing -> evalFail' (EvalSubstitution m) [Var v]
    subAllRun _    _ t@(Asymm _ _)= evalFail' EvalMalformed [t]
    subAllRun prog m (Compound t) = fmap Compound <$> subAllRun prog m t

    evaluate = evaluateLocal' . evaluate

    compatible (Var _)      _             = True
    compatible _            (Var _)       = True
    compatible a@(Atom _ _) b@(Atom _ _)  = a == b
    compatible (Asymm l r)  t             = compatible l t || compatible r t
    compatible t            a@(Asymm _ _) = compatible a t
    compatible (Compound s) (Compound t)  = compatible s t
    compatible _            _             = False

instance Kappa Context where
    asplit (Context c p) = let (c1,c2) = asplit c
                               (p1,p2) = asplit p
                           in (Context c1 p1, Context c2 p2)

    vars' (Context c p)= M.unionWith (+) (vars' c) (vars' p)
    vars (Context c p) = S.union (vars c) (vars p)

    unify p (Context c1 p1) (Context c2 p2) = unify p (c1:p1) (c2:p2)
    unifyDup p (Context c1 p1) (Context c2 p2) = unifyDup p (c1:p1) (c2:p2)

    sub m (Context c p) = let (m',c') = sub m c
                              (m'',p') = sub m' p
                          in (m'', Context c' p')

    subAll m (Context v@(Var _) p) = let (m',v') = sub m v
                                     in fmap (Context v') <$> subAll m' p
    subAll m (Context c p)         = do (m',c') <- subAll m c
                                        (m'',p') <- subAll m' p
                                        return (m'', Context c' p')

    subAllDup m (Context c p) = go <$> subAllDup m (c:p)
      where go (c':p') = Context c' p'
            go []      = undefined

    subAllRun prog m (Context v@(Var _) p) =
      let (m',v') = sub m v in fmap (Context v') <$> subAllRun1 prog m' p
    subAllRun prog m x@(Context c p) =
      do (m',c') <- evalMaybe (EvalSubstitution m) [x] $ subAll m c
         fmap (Context c') <$> subAllRun1 prog m' p

    evaluate = evaluateContext

    compatible (Context c1 p1) (Context c2 p2) = compatible c1 c2 && compatible p1 p2

-- compilation

    -- (curr label, inverse label, stratagem)
newtype Program = Program [(Int,Int,Strategy)]

data Strategy = StratHalt [Term]
              | Strategy { _stLPatt :: [Context]
                         , _stRules :: Vector Context
                         , _stPlan  :: [Either Int Int]
                         , _stRPatt :: [Context] }

data CompilationError = ParseError PE.ParseError
                      | AmbiguityError [Definition]
                      | ReversibilityError [Definition]
                      | VarConflictError [Definition]

instance Show Strategy where
    show (StratHalt t) = show (Terminus t)
    show (Strategy l d p r) = showStratHead l r ++ showRules showp p
      where showp (Left  n) = "< " ++ show (d ! n) ++ "."
            showp (Right n) = "> " ++ show (d ! n) ++ "."

showStratHead l r =
    case ruleInfixP r l of
        Just _  -> "< " ++ showRuleHead r l
        Nothing -> "> " ++ showRuleHead l r

instance Show Program where
    show (Program xs) = showMany "\n" xs

instance Show CompilationError where
    show (ParseError e) = "Parse error!: " ++ show e
    show (AmbiguityError d) = "Non-determinism detected within the following rules:" ++ showErrDefs d
    show (ReversibilityError d) = "Couldn't find a reversible execution plan for the following:" ++ showErrDefs d
    show (VarConflictError d) = "Conflicting variables in the following:" ++ showErrDefs d

stripChildren :: Definition -> Definition
stripChildren (Terminus t) = Terminus (t)
stripChildren (Rule l r _) = Rule l r []

showErrDefs :: [Definition] -> String
showErrDefs = concatMap (("\n    "++) . show . stripChildren)

-- evaluation

data EvalStatus = EvalOk
                | EvalStuck
                | EvalUnification  [Context]
                | EvalSubstitution (Map String Term)
                | EvalUnconsumed   (Map String Term)
                | EvalAmbiguous
                | EvalUndefined
                | EvalBadInitial
                | EvalMalformed
                | EvalMulti
                | EvalCorrupt

instance Show EvalStatus where
    show EvalOk        = "Evaluation successfully halted."
    show EvalStuck     = "No successor found, evaluation stuck."
    show (EvalUnification c) = "Couldn't unify against " ++ showCtxts c ++ "."
    show (EvalSubstitution v) = "Couldn't substitute using {\n" ++ showVars v ++ "}."
    show (EvalUnconsumed v) = "Incomplete substitution, {\n" ++ showVars v ++ "}."
    show EvalAmbiguous = "Non-determinism encountered, successor state is ambiguous."
    show EvalUndefined = "Term or one of its subterms is undefined."
    show EvalBadInitial= "Cannot construct a non-halting term, perhaps you forgot to declare a halting state?"
    show EvalMalformed = "Malformed input, perhaps an unexpected variable or asymmetry."
    show EvalMulti     = "Multiple parties encountered, this is not supported."
    show EvalCorrupt   = "Unexpected internal error..."


data EvalStack' t a = EvalSuccess a
                    | EvalStack (Maybe a) [(EvalStatus, t)]
type EvalStack = EvalStack' [Context] [Context]

instance (Show t, Show a) => Show (EvalStack' t [a]) where
  show (EvalSuccess x) = showSp x
  show (EvalStack x e) = "Evaluation Error:\n" ++ indent 2 (concatMap go e) ++ go' x
    where go (m,y) = show m ++ "\n  " ++ show y ++ "\n"
          go' Nothing = ""
          go' (Just y) = showSp y

instance Functor (EvalStack' t) where
  f `fmap` EvalSuccess x = EvalSuccess (f x)
  f `fmap` EvalStack x s = EvalStack (f <$> x) s

instance Applicative (EvalStack' t) where
  pure = EvalSuccess

  EvalSuccess f <*> EvalSuccess x = EvalSuccess (f x)
  EvalSuccess f <*> EvalStack x s = EvalStack (f <$> x) s
  EvalStack f s <*> EvalSuccess x = EvalStack (f <*> pure x) s
  EvalStack f s <*> EvalStack x t = EvalStack (f <*> x) (s ++ t)

instance Monad (EvalStack' t) where
  EvalSuccess x >>= f = f x
  EvalStack x s >>= f = case f <$> x of
                          Just (EvalSuccess y) -> EvalStack (Just y) s
                          Just (EvalStack y t) -> EvalStack y (s ++ t)
                          Nothing              -> EvalStack Nothing s

evalMaybe :: EvalStatus -> t -> Maybe a -> EvalStack' t a
evalMaybe s t Nothing  = EvalStack Nothing [(s,t)]
evalMaybe _ _ (Just x) = EvalSuccess x

evalFail :: EvalStatus -> t -> EvalStack' t a
evalFail s t = EvalStack Nothing [(s,t)]
evalFail' s = evalFail s . pure . Context (Var "??")

evalPartial :: (Show t, Show a) => EvalStack' t [a] -> Either t [a]
evalPartial (EvalSuccess x)        = Right x
evalPartial v | trace ("ep: " ++ show v) False = undefined
evalPartial (EvalStack (Just x) _) = Right x
evalPartial (EvalStack Nothing  s) =
  case s of (_,t):_ -> Left t
            _       -> error "evalPartial: all state lost !?"

match :: Program -> [Context] -> [(Int,Int,Strategy)]
match (Program [])     _ = []
match (Program (x@(_,_,x'):xs)) c =
    let rest = match (Program xs) c
    in case x' of
        StratHalt p       | compatible [p] (map _cTerm c) -> x : rest
        Strategy  p _ _ _ | compatible  p  c              -> x : rest
        _                                                 ->     rest

isHalting :: Program -> [Term] -> Bool
isHalting (Program []) _       = False
isHalting (Program ((_,_,StratHalt x) : _)) c
    | compatible x c           = True
isHalting (Program (_ : xs)) c = isHalting (Program xs) c

-- the status output indicates whether or not the computation successfully completed
-- evaluate requires its input to be in a halting state (i.e. an initial
--    state) so that it can deterministically pick an execution direction
evaluateContext :: Program -> [Context] -> EvalStack
evaluateContext _ [Context c [Compound [x, y], z]]
    | x == atomDup && z == termTerm
        = return [Context c [z, y, Compound [x, y]]]
evaluateContext _ [Context c [z, y, Compound [x, y']]]
    | x == atomDup && z == termTerm && y == y'
        = return [Context c [Compound [x, y], z]]
evaluateContext prog entity =
  case partition haltp (match prog entity) of
    (_:_,[_]) -> evaluate' prog (-1) entity
    (_:_,[])  -> return entity
    (_:_,_)   -> evalFail EvalAmbiguous  entity
    ([],[])   -> evalFail EvalUndefined  entity
    ([],_)    -> evalFail EvalBadInitial entity

haltp (_,_,StratHalt _) = True
haltp _                 = False

-- evaluate' takes a previous strategy (Int) and continues in the same direction
evaluate' :: Program -> Int -> [Context] -> EvalStack
evaluate' prog prev entity =
  case partition haltp (match prog entity) of
    (_:_,[])                                -> return entity
    (_,[(m,m',s)])             | m' == prev -> return entity
                               | otherwise  -> go m s
    ([],[(m,m',s1),(n,n',s2)]) | m' == prev -> go n s2
                               | n' == prev -> go m s1
    (xs,ys)                    | any successor (xs ++ ys)
                                            -> evalFail EvalAmbiguous entity
    ([],[])                                 -> evalFail EvalStuck     entity
    _                                       -> evalFail EvalCorrupt   entity
  where
    go _ (StratHalt _) = return entity
    go n s = eval prog s entity >>= evaluate' prog n
    successor (_,n,_) = n == prev

eval :: Program -> Strategy -> [Context] -> EvalStack
-- eval _ s e | trace ("eval: " ++ show (s,e)) False = undefined
eval _    (StratHalt _)                 lent = pure lent
eval prog (Strategy lhs rules plan rhs) lent =
  do
    lvars <- evalMaybe (EvalUnification lhs) lent $ unify ishp lhs lent
    rvars <- foldM execute lvars plan'
    (vars0,rent) <- subAllRun1 prog rvars rhs
    -- trace ("eval': " ++ show (lent,rent)) $
    if M.null vars0 then return rent else EvalStack Nothing [(EvalUnconsumed vars0, rent)]
  where
    ishp = isHalting prog
    goPlan ridx = let (Context (Var v) patt) = rules ! ridx in (v, patt)
    plan' = map (either2 goPlan) plan
    cv v p = [Context (Var v) p]

    -- execute v c | trace ("evalx: " ++ show(lent,v,c)) False = undefined
    execute mvars (False, (v, patt)) =
      do (mvars',ent) <- subAllRun prog mvars patt
         return $ M.insert v (Compound ent) mvars'
    execute mvars (True,  (v, patt)) =
      do (mvars',t)   <- evalMaybe EvalCorrupt (cv v patt) $ subAll mvars (Var v)
         case t of
            Compound ent -> evalMaybe (EvalUnification $ cv v patt) (cv v ent)
                          $ unify ishp patt ent >>= mapMergeDisjoint mvars'
            _ -> EvalStack Nothing [(EvalCorrupt, cv v [t])]

evaluateRec :: Program -> [Context] -> EvalStack
evaluateRec prog = mapM goc
  where
    goc (Context c ent) = go (Compound ent) >>= \case
                            Compound ent' -> return $ Context c ent'
                            t            -> evalFail EvalCorrupt [Context c [t]]

    go (Compound ts) = Compound <$> (mapM go ts >>= evaluate prog)
    go x@(Asymm _ _) = evalFail EvalMalformed [Context (Var "") [x]]
    go x             = return x

evaluateLocal' :: ([Context] -> EvalStack) -> [Term] -> EvalStack' [Context] [Term]
evaluateLocal' eval' ts =
    let c = phony "<|local|>"
        x = [Context c ts]
    in eval' x >>= \case
        r@[Context c' ts'] | c == c'   -> return ts'
                           | otherwise -> evalFail EvalCorrupt r
        _                              -> evalFail EvalMulti   x

evaluateRecLocal :: Program -> [Term] -> EvalStack' [Context] [Term]
evaluateRecLocal = evaluateLocal' . evaluateRec