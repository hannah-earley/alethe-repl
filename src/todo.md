# Todo

- Parser
    - we should do all scoping and imports within parser
    - otherwise have to redescend to sort out scoped atoms
    - also have to pull out subdefs into global namespace
    - also need to somehow track scope numbers etc

```
data ParseState = ParseState
  { scopeCounter :: Integer
  , scopeStack :: [Integer]
  , seenFiles :: Set ResourceID
  }

withState :: ParsecT s u m a -> ParsecT s u m (a,s)
withState p = liftM2 (,) p getState

import :: FilePath -> ParsecT ParseState u IO [Definition]
import name = do st <- getState
                 fd <- liftIO $ open name
                 let rid = resid fd

                 if rid `in` seenFiles st
                   then close fd
                   else do
                     handle <- fdToHandle fd
                     contents <- hGetContents handle
                     hClose handle

                     runParserT (withState prog) name (st { seenFiles = ... }) >>= \case
                        Left e ->
                        Right (x, st') -> putState st' >> return x





```