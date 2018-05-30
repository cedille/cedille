module Main where
import Check
import Ctxt
import Norm
import Parser
import ToString
import Types
import System.FilePath
import System.Directory

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
  checkFile (ctxtShowAll c emptyTrie) fs ifp >>= \ (c', fs') ->
  let ds = trieAdd (ctxtShown c) (ctxtShown c') in
  return (Right (ctxtShowAll c' ds, trieInsert fs' fp ds))

--checkCmds :: Cmds -> Ctxt -> Trie (Trie ()) -> String -> IO (Either String (Ctxt, Trie (Trie ())))
checkCmds CmdsStart ctxt fs fp = return (Right (ctxt, fs))
checkCmds (CmdsNext c cs) ctxt fs fp = checkCmd c ctxt fs fp >>= \ r -> case r of
  Right (ctxt', fs') -> checkCmds cs ctxt' fs' fp
  err -> return err

--checkFile :: Ctxt -> Trie (Trie ()) -> String -> IO (Ctxt, Trie (Trie ()))
checkFile c fs fp =
  getCurrentDirectory >>= \ cd ->
  makeAbsolute (cd </> fp <.> "ced") >>= \ fp' ->
  setCurrentDirectory (takeDirectory fp') >>
  case trieLookup fs fp' of
    Just ds -> return (ctxtShowAll c ds, fs)
    Nothing ->
      let msg = putStrLn . (++) ("[" ++ fp' ++ "] ")
          fs' = trieInsert fs fp' emptyTrie in
      doesFileExist fp' >>= \ exists ->
      if not exists
        then msg "File does not exists" >> return (c, fs')
        else readFile fp' >>= \ s -> maybe
          (msg "Parse error" >> return (c, fs'))
          (\ (cs, _) ->
             checkCmds cs c fs' fp' >>= \ r -> case r of
               Left err -> msg err >> return (c, fs')
               Right c' -> msg "No errors" >> return c')
          (lexStr s >>= parseMf (parseDropModule *> parseCmds))

--splitStr :: String -> String -> [String]
splitStr s [] = s : []
splitStr s (' ' : cs) = s : splitStr "" cs
splitStr s (c : cs) = splitStr (s ++ (c : [])) cs

--joinStr :: [String] -> String
joinStr [] = ""
joinStr (s : []) = s
joinStr (s : ss) = s ++ " " ++ joinStr ss

--handleInput :: Ctxt -> [String] -> IO ()
handleInput c ("check" : fp : []) = checkFile emptyCtxt emptyTrie fp >>= mainWithCtxt . fst
handleInput c ("lookup" : "term" : "hnf" : v : []) = putStrLn (maybe "Term not defined" show (ctxtLookupTermVar c v)) >> mainWithCtxt c
handleInput c ("lookup" : "type" : "hnf" : v : []) = putStrLn (maybe "Type not defined" show (ctxtLookupTypeVar c v)) >> mainWithCtxt c
handleInput c ("lookup" : "term" : "type" : v : []) = putStrLn (maybe "Term not defined" show (ctxtLookupVarType c v)) >> mainWithCtxt c
handleInput c ("lookup" : "type" : "kind" : v : []) = putStrLn (maybe "Type not defined" show (ctxtLookupVarKind c v)) >> mainWithCtxt c
handleInput c ("quit" : []) = return ()
handleInput c _ = putStrLn "Unknown command" >> mainWithCtxt c

mainWithCtxt c = getLine >>= handleInput c . splitStr ""

main = mainWithCtxt emptyCtxt
