{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}

module Magic where
import Language
import Data.Set (Set)
import qualified Data.Set as S
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import Control.Exception (IOException, catch)
import Data.Typeable (Typeable, cast)

data MagicRule = MagicRule { mrLHS, mrRHS :: Set String
                           , mrFwd, mrBwd :: MagicExec
                           , mrHelp :: String }

magic1monad :: Typeable m => MagicExec' m -> MagicExec
magic1monad mag = \t x -> case cast (mag t x) of
                          Just y -> y
                          Nothing -> evalFailM EvalWrongMonad []

magicpure :: ([Context] -> Map String Term -> EvalStack' [Context] (Map String Term)) -> MagicExec
magicpure mag = \t x -> EvalStackT' $ return (mag t x)

magicLookup :: String -> Maybe MagicRule
magicLookup "io.file.read" = Just $
  MagicRule { mrLHS = S.fromList ["path"]
            , mrRHS = S.fromList ["path", "contents"]
            , mrFwd = magic1monad (\t v -> do
                p <- liftMaybe t (EvalSubstitution v) (v M.!? "path")
                p' <- liftMaybe t (EvalOther $ "io.file.read: expecting string path, not " ++ show p) (str' p)
                c <- safeReadFile t p'
                disjointInsert t v "contents" (str c))
            , mrBwd = magic1monad (\t v -> do
                p <- liftMaybe t (EvalSubstitution v) (v M.!? "path")
                p' <- liftMaybe t (EvalOther $ "io.file.read: expecting string path, not " ++ show p) (str' p)
                (c, v') <- liftMaybe t (EvalSubstitution v) (pop "contents" v)
                c' <- liftMaybe t (EvalOther $ "io.file.read: expecting string contents, not " ++ show c) (str' c)
                c'' <- safeReadFile t p'
                if c' == c''
                  then return v'
                  else evalFailM (EvalOther $ "io.file.read: couldn't unread file " ++ p' ++ " because the contents differ (maybe it changed on disk?)") t)
            , mrHelp = "Copy contents of file \"path\" into variable \"contents\""
            }
magicLookup "data.any.dup" = Just $
  MagicRule { mrLHS = S.fromList ["orig"]
            , mrRHS = S.fromList ["orig", "copy"]
            , mrFwd = (\t v -> do
                x <- liftMaybe t (EvalSubstitution v) (v M.!? "orig")
                disjointInsert t v "copy" x)
            , mrBwd = (\t v -> do
                x <- liftMaybe t (EvalSubstitution v) (v M.!? "orig")
                (x', v') <- liftMaybe t (EvalSubstitution v) (pop "copy" v)
                if x == x'
                  then return v'
                  else evalFailM (EvalOther $ "data.any.dup: values differ:\n  " ++ show x ++ "\n  " ++ show x') t)
            , mrHelp = "Implement duplication for all values" }
magicLookup "data.any.eq" = Just $
  MagicRule { mrLHS = S.fromList ["x", "y"]
            , mrRHS = S.fromList ["x", "y", "p"]
            , mrFwd = (\t v -> do
                x <- liftMaybe t (EvalSubstitution v) (v M.!? "x")
                y <- liftMaybe t (EvalSubstitution v) (v M.!? "y")
                let p = if x == y then atomTrue else atomFalse
                disjointInsert t v "p" p)
            , mrBwd = (\t v -> do
                x <- liftMaybe t (EvalSubstitution v) (v M.!? "x")
                y <- liftMaybe t (EvalSubstitution v) (v M.!? "y")
                (p, v') <- liftMaybe t (EvalSubstitution v) (pop "p" v)
                if x == y
                  then (if p == atomTrue then return v' else evalFailM (EvalOther $ "data.any.eq: expecting True, got " ++ show p) t)
                  else (if p == atomFalse then return v' else evalFailM (EvalOther $ "data.any.eq: expecting False, got " ++ show p) t))
            , mrHelp = "Implement equality testing for all values" }
magicLookup _ = Nothing

safeReadFile' :: FilePath -> IO (Either String String)
safeReadFile' f =
  catch (Right <$> readFile f) (\e -> return . Left $ show (e :: IOException))

safeReadFile :: t -> FilePath -> EvalStackT' IO t String
safeReadFile t f = do
  c <- liftEval (safeReadFile' f)
  case c of
    Right c' -> return c'
    Left e -> evalFailM (EvalOther $ "io.file.read: error trying to read " ++ f ++ ": " ++ e) t

pop :: Ord k => k -> Map k v -> Maybe (v, Map k v)
pop k m = (, M.delete k m) <$> m M.!? k

liftMaybe :: AMConstraint m => t -> EvalStatus -> Maybe a -> EvalStackT' m t a
liftMaybe t err = maybe (evalFailM err t) return

assertNoVar :: AMConstraint m => t -> Map String v -> String -> EvalStackT' m t ()
assertNoVar t m k = maybe (pure ()) (const $ evalFailM err t) $ m M.!? k
  where err = EvalVarConflict [k]

disjointInsert :: AMConstraint m => t -> Map String v -> String -> v -> EvalStackT' m t (Map String v)
disjointInsert t m k v = assertNoVar t m k >> return (M.insert k v m)