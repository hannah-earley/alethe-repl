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



magicLookup :: String -> Maybe MagicRule
magicLookup "io.file.read" = Just $
  MagicRule { mrLHS = S.fromList ["path"]
            , mrRHS = S.fromList ["path", "contents"]
            , mrFwd = magic1monad (\t v -> do
                p <- liftMaybe t (EvalSubstitution v) (v M.!? "path")
                p' <- liftMaybe t (EvalOther $ "io.file.read: expecting string path, not " ++ show p) (str' p)
                c <- safeReadFile t p'
                return $ M.insert "contents" (str c) v)
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