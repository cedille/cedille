module Main where
import Check
import Ctxt
import Norm
import Parser
import ToString
import Types
import System.FilePath
import System.Directory
import System.Environment

--maybeAddDef :: Trie (Trie ()) -> FilePath -> Var -> Trie (Trie ())
maybeAddDef fs fp v = trieInsert fs fp (maybe emptyTrie (\ ds -> trieInsert ds v ()) (trieLookup fs fp))

--checkCmd :: Cmd -> Ctxt -> Trie (Trie ()) -> String -> IO (Either String (Ctxt, Trie (Trie ())))
checkCmd (TermCmd v tm) c fs fp = return $
  if ctxtBindsVar c v then Left ("Multiple definitions of variable " ++ v) else Right () >>
  synthTerm c tm >>= \ tp ->
  Right (ctxtDefTerm c v (Just (hnfeTerm c tm), Just (hnfType c tp)), maybeAddDef fs fp v)
checkCmd (TypeCmd v kd tp) c fs fp = return $
  if ctxtBindsVar c v then Left ("Multiple definitions of variable " ++ v) else Right () >>
  synthType c tp >>= \ kd' ->
  errIfNot (convKind c (eraseKind kd) kd') ("The expected kind does not match the synthesized kind, in the definition of " ++ v) >>
  Right (ctxtDefType c v (Just (hnfeType c tp), Just (hnfKind c kd')), maybeAddDef fs fp v)
checkCmd (ImportCmd ifp) c fs fp =
  checkFile (ctxtShowAll c emptyTrie) fs ifp >>= \ mcfs -> case mcfs of
    Nothing -> return (Left "")
    Just (c', fs') ->
      let ds = trieAdd (ctxtShown c) (ctxtShown c') in
      return (Right (ctxtShowAll c' ds, trieInsert fs' fp ds))

--checkCmds :: Cmds -> Ctxt -> Trie (Trie ()) -> String -> IO (Either String (Ctxt, Trie (Trie ())))
checkCmds CmdsStart ctxt fs fp = return (Right (ctxt, fs))
checkCmds (CmdsNext c cs) ctxt fs fp = checkCmd c ctxt fs fp >>= \ r -> case r of
  Right (ctxt', fs') -> checkCmds cs ctxt' fs' fp
  err -> return err

--checkFile :: Ctxt -> Trie (Trie ()) -> String -> IO (Maybe (Ctxt, Trie (Trie ())))
checkFile c fs fp =
  getCurrentDirectory >>= \ cd ->
  makeAbsolute (cd </> fp -<.> "ced") >>= \ fp' ->
  setCurrentDirectory (takeDirectory fp') >>
  case trieLookup fs fp' of
    Just ds -> return (Just (ctxtShowAll c ds, fs))
    Nothing ->
      let msg = putStrLn . (++) ("[" ++ fp' ++ "] ")
          fs' = trieInsert fs fp' emptyTrie in
      doesFileExist fp' >>= \ exists ->
      if not exists
        then msg "File does not exists" >> return Nothing
        else readFile fp' >>= \ s -> maybe
          (msg "Parse error" >> return Nothing)
          (\ (cs, _) ->
             checkCmds cs c fs' fp' >>= \ r -> case r of
               Left ""  -> return Nothing
               Left err -> msg err >> return Nothing
               Right c' -> msg "No errors" >> return (Just c'))
          (lexStr s >>= parseMf (parseDropModule *> parseCmds))

main = getArgs >>= \ as -> case as of
  (fp : []) -> checkFile emptyCtxt emptyTrie fp >> return ()
  _ -> putStrLn "Run with the name of a single file"
