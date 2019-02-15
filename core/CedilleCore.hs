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
import System.Exit

--maybeAddDef :: Trie (Trie ()) -> FilePath -> Var -> Trie (Trie ())
maybeAddDef fs fp v = trieInsert fs fp (maybe emptyTrie (\ ds -> trieInsert ds v ()) (trieLookup fs fp))

--checkCmd :: Cmd -> Bool -> Ctxt -> Trie (Trie ()) -> String -> IO (Either String (Ctxt, Trie (Trie ())))
checkCmd (TermCmd v tm) b c fs fp = return $
  if ctxtBindsVar c v then Left ("Multiple definitions of variable " ++ v) else Right () >>
  synthTerm c tm >>= \ tp ->
  Right (ctxtDefTerm c v (Just (hnfeTerm c tm), Just (hnfType c tp)), maybeAddDef fs fp v)
checkCmd (TypeCmd v kd tp) b c fs fp = return $
  if ctxtBindsVar c v then Left ("Multiple definitions of variable " ++ v) else Right () >>
  synthType c tp >>= \ kd' ->
  errIfNot (convKind c (eraseKind kd) kd') ("The expected kind does not match the synthesized kind, in the definition of " ++ v) >>
  Right (ctxtDefType c v (Just (hnfeType c tp), Just (hnfKind c kd')), maybeAddDef fs fp v)
checkCmd (ImportCmd ifp) b c fs fp =
  checkFile b (ctxtShowAll c emptyTrie) fs ifp >>= \ mcfs -> case mcfs of
    Nothing -> return (Left "")
    Just (c', fs') ->
      let ds = trieAdd (ctxtShown c) (ctxtShown c') in
      return (Right (ctxtShowAll c' ds, trieInsert fs' fp ds))

--checkCmds :: Cmds -> Bool -> Ctxt -> Trie (Trie ()) -> String -> IO (Either String (Ctxt, Trie (Trie ())))
checkCmds CmdsStart b ctxt fs fp = return (Right (ctxt, fs))
checkCmds (CmdsNext c cs) b ctxt fs fp = checkCmd c b ctxt fs fp >>= \ r -> case r of
  Right (ctxt', fs') -> checkCmds cs b ctxt' fs' fp
  err -> return err

--checkFile :: Bool -> Ctxt -> Trie (Trie ()) -> String -> IO (Maybe (Ctxt, Trie (Trie ())))
checkFile b c fs fp =
  getCurrentDirectory >>= \ cd ->
  makeAbsolute (cd </> fp -<.> "cdle") >>= \ fp' ->
  setCurrentDirectory (takeDirectory fp') >>
  case trieLookup fs fp' of
    Just ds -> return (Just (ctxtShowAll c ds, fs))
    Nothing ->
      let msg = putStrLn . (++) ("[" ++ fp' ++ "] ")
          checks = if b then return () else msg "No errors"
          nchecks = \ e -> if b then exitWith exitTypeError else msg e
          nexists = if b then exitWith exitFileDoesNotExist else msg "File does not exist"
          nparses = if b then exitWith exitParseError else msg "Parse error"
          fs' = trieInsert fs fp' emptyTrie in
      doesFileExist fp' >>= \ exists ->
      if not exists
        then nexists >> return Nothing
        else readFile fp' >>= \ s -> maybe
          (nparses >> return Nothing)
          (\ (cs, _) ->
             checkCmds cs b c fs' fp' >>= \ r -> case r of
               Left ""  -> return Nothing
               Left err -> nchecks err >> return Nothing
               Right c' -> checks >> return (Just c'))
          (lexStr s >>= parseMf (parseDropModule *> parseCmds))

exitOptionsError = ExitFailure 1
exitParseError = ExitFailure 2
exitFileDoesNotExist = ExitFailure 3
exitTypeError = ExitFailure 4
exitTypeChecks = ExitSuccess

helpStr =
  "cedille-core [OPTIONS] [FILE]\n  " ++
  "-b --binary    exit with error code if an error is encountered (0 = type checks; 1 = options error; 2 = parse error; 3 = file does not exist; 4 = type error)\n  " ++
  "-h --help      print this help message (the above option looked lonely all by itself)"

data Option =
    Binary
  | Help
  | Unknown String

mkOption str opt opts = trieInsert opts str opt

--options :: Trie Option
options = mkOption "-b" Binary $ mkOption "--binary" Binary $ mkOption "-h" Help $ mkOption "--help" Help emptyTrie

--filterArgs :: [String] -> ([Option], [String])
filterArgs [] = ([], [])
filterArgs (('-' : cs) : as) =
  let (opts, fps) = filterArgs as in
  (maybe (Unknown ('-' : cs)) id (trieLookup options ('-' : cs)) : opts, fps)
filterArgs (fp : as) =
  let (opts, fps) = filterArgs as in
  (opts, (fp : fps))

filterArgsAux as = case filterArgs as of
  (opts, []) -> (Help : [], [])
  x          -> x

argsHaveBinary [] = return False
argsHaveBinary (Help : as) = putStrLn helpStr >> argsHaveBinary as
argsHaveBinary (Binary : as) = argsHaveBinary as >> return True
argsHaveBinary (Unknown a : as) = putStrLn helpStr >> putStrLn ("Unknown option \"" ++ a ++ "\"") >> exitWith exitOptionsError

main =
  getArgs >>= \ as ->
  let (opts, fps) = filterArgsAux as in
  argsHaveBinary opts >>= \ b ->
  foldr (\ fp io -> checkFile b emptyCtxt emptyTrie fp >> io) (return ()) fps >>
  if b then exitWith exitTypeChecks else return ()
