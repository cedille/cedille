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

-- ModInfo (Module scope) (Filepath) (Context) (Binary?, Verbose?, Indentation)
data ModInfo = ModInfo (Trie (Trie ())) FilePath Ctxt (Bool, Bool, Int)

--maybeAddDef :: Var -> ModInfo -> ModInfo
maybeAddDef v (ModInfo fs fp c o) =
  ModInfo (trieInsert fs fp (maybe emptyTrie (\ ds -> trieInsert ds v ()) (trieLookup fs fp))) fp c o

putMsg tab fp msg = putStrLn $ replicate tab ' ' ++ "[" ++ fp ++ "] " ++ msg

--checkCmd :: Cmd -> ModInfo -> IO (Either String ModInfo)
checkCmd (TermCmd v tm) (ModInfo fs fp c o@(bin, vrb, tab)) =
  (>>) (if vrb && not bin then putMsg tab fp ("Checking " ++ v) else return ()) $ return $
  if ctxtBindsVar c v then Left ("Multiple definitions of variable " ++ v) else Right () >>
  synthTerm c tm >>= \ tp ->
  Right (maybeAddDef v $ ModInfo fs fp
         (ctxtDefTerm c v (Just (hnfeTerm c tm), Just (hnfType c tp))) o)
checkCmd (TypeCmd v kd tp) (ModInfo fs fp c o@(bin, vrb, tab)) =
  (>>) (if vrb && not bin then putMsg tab fp ("Checking " ++ v) else return ()) $ return $
  if ctxtBindsVar c v then Left ("Multiple definitions of variable " ++ v) else Right () >>
  synthType c tp >>= \ kd' ->
  errIfNot (convKind c (eraseKind kd) kd')
    ("The expected kind does not match the synthesized kind, in the definition of " ++ v) >>
  Right (maybeAddDef v $ ModInfo fs fp
         (ctxtDefType c v (Just (hnfeType c tp), Just (hnfKind c kd'))) o)
checkCmd (ImportCmd ifp) (ModInfo fs fp c o) =
  checkFile (ModInfo fs ifp (ctxtShowAll c emptyTrie) o) >>= maybe (return $ Left "")
  (\ (ModInfo fs' _ c' _) ->
     let ds = trieAdd (ctxtShown c) (ctxtShown c') in
     return (Right $ ModInfo (trieInsert fs' fp ds) fp (ctxtShowAll c' ds) o))

--checkCmds :: Cmds -> ModInfo -> IO (Either String ModInfo)
checkCmds CmdsStart m = return $ Right m
checkCmds (CmdsNext c cs) m = checkCmd c m >>= either (return . Left) (checkCmds cs)

--checkFile :: ModInfo -> IO (Maybe ModInfo)
checkFile (ModInfo fs fp c (b, v, i)) =
  getCurrentDirectory >>= \ cd ->
  makeAbsolute (cd </> fp -<.> "cdle") >>= \ fp' ->
  setCurrentDirectory (takeDirectory fp') >>
  case trieLookup fs fp' of
    Just ds -> return (Just $ ModInfo fs fp (ctxtShowAll c ds) (b, v, i))
    Nothing ->
      let msg s e = if b then e else putMsg i fp' s
          checks = msg "No errors" (return ())
          nchecks = flip msg $ exitWith exitTypeError
          nexists = msg "File does not exist" $ exitWith exitFileDoesNotExist
          nparses = msg "Parse error" $ exitWith exitParseError
          fs' = trieInsert fs fp' emptyTrie in
      msg "Checking" (return ()) >>
      doesFileExist fp' >>= \ exists ->
      if not exists
        then nexists >> return Nothing
        else readFile fp' >>= \ s -> maybe
          (nparses >> return Nothing)
          (\ (cs, _) ->
             checkCmds cs (ModInfo fs' fp' c (b, v, succ i)) >>= \ r -> case r of
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
  maybe "" id $ foldr (\ ln -> Just . maybe ln (ln ++)) Nothing
    ["cedille-core [OPTIONS] [FILE]",
     "  -b --binary    exit with error code if an error is encountered",
     "                 (0 = type checks; 1 = options error; 2 = parse error;",
     "                  3 = file does not exist; 4 = type error)",
     "  -v --verbose   enable verbose messages",
     "  -h --help      print this help message"]


--             Options File Binary Verbose
data Options = Options FilePath Bool Bool | Help | Unknown String

mapOpts f o@(Options _ _ _) = f o
mapOpts _ o = o

mkOption short long opt opts = trieInsert (trieInsert opts long opt) short opt

--options :: Trie Option
options =
  mkOption "-b" "--binary"  (\ (Options f b v) -> Options f True v) $
  mkOption "-v" "--verbose" (\ (Options f b v) -> Options f b True) $
  mkOption "-h" "--help"    (\ _ -> Help) $
  emptyTrie

--readArgs :: Options -> [String] -> Options
readArgs opts (a@('-' : _) : as) =
  maybe (Unknown a) (\ f -> mapOpts (flip readArgs as . f) opts) (trieLookup options a)
readArgs (Options "" b v) (fp : as) = readArgs (Options fp b v) as
readArgs (Options _ _ _) (fp : as) = Help
readArgs opts _ = opts

readArgsAux as = case readArgs (Options "" False False) as of
  Options "" b v -> Help
  opts           -> opts

main =
  getArgs >>= \ as ->
  case readArgsAux as of
    opts@(Options f b v) ->
      checkFile (ModInfo emptyTrie f emptyCtxt (b, v, 0)) >>
      if b then exitWith exitTypeChecks else return ()
    Help -> putStrLn helpStr
    Unknown a -> putStrLn ("Unknown option \"" ++ a ++ "\"") >> putStrLn helpStr

