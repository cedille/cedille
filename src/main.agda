module main where

open import lib
import string-format
-- for parser for Cedille 
open import cedille-types

-- for parser for options files
import options-types
import cedille-options

-- for parser for Cedille comments & whitespace
import cws-types

open import constants
open import general-util


createOptionsFile : (dot-ced-dir : string) → IO ⊤
createOptionsFile dot-ced-dir =
  let ops-fp = combineFileNames dot-ced-dir options-file-name in
  createDirectoryIfMissing ff (takeDirectory ops-fp) >>
  withFile ops-fp WriteMode (flip hPutRope (cedille-options.options-to-rope cedille-options.default-options))

str-bool-to-𝔹 : options-types.str-bool → 𝔹
str-bool-to-𝔹 options-types.StrBoolTrue = tt
str-bool-to-𝔹 options-types.StrBoolFalse = ff

opts-to-options : filepath → options-types.opts → IO cedille-options.options
opts-to-options ofp (options-types.OptsCons (options-types.Lib fps) ops) =
  opts-to-options ofp ops >>= λ ops → paths-to-stringset fps >>=r λ ip → record ops { include-path = ip }
  where relative-to-options : filepath → filepath
        relative-to-options fp with string-to-𝕃char fp
        ...| '.' :: '.' :: c :: cs =
          if c =char pathSeparator
            then combineFileNames (takeDirectory ofp) fp
            else fp
        ...| _ = fp
        paths-to-stringset : options-types.paths → IO (𝕃 string × stringset)
        paths-to-stringset (options-types.PathsCons fp fps) =
          canonicalizePath (relative-to-options fp) >>= λ cfp →
          paths-to-stringset fps >>=r cedille-options.include-path-insert cfp
        paths-to-stringset options-types.PathsNil = return ([] , empty-stringset)
opts-to-options ofp (options-types.OptsCons (options-types.UseCedeFiles b) ops) =
  opts-to-options ofp ops >>=r λ ops → record ops { use-cede-files = str-bool-to-𝔹 b }
opts-to-options ofp (options-types.OptsCons (options-types.MakeRktFiles b) ops) =
  opts-to-options ofp ops >>=r λ ops → record ops { make-rkt-files = str-bool-to-𝔹 b }
opts-to-options ofp (options-types.OptsCons (options-types.GenerateLogs b) ops) =
  opts-to-options ofp ops >>=r λ ops → record ops { generate-logs = str-bool-to-𝔹 b }
opts-to-options ofp (options-types.OptsCons (options-types.ShowQualifiedVars b) ops) =
  opts-to-options ofp ops >>=r λ ops → record ops { show-qualified-vars = str-bool-to-𝔹 b }
opts-to-options ofp (options-types.OptsCons (options-types.EraseTypes b) ops) =
  opts-to-options ofp ops >>=r λ ops → record ops { erase-types = str-bool-to-𝔹 b }
opts-to-options ofp options-types.OptsNil = return cedille-options.default-options

-- helper function to try to parse the options file
processOptions : filepath → string → IO (string ⊎ cedille-options.options)
processOptions filename s with options-types.scanOptions s
...| options-types.Left cs = return (inj₁ ("Parse error in file " ^ filename ^ " " ^ cs ^ "."))
...| options-types.Right (options-types.File oo) = opts-to-options filename oo >>=r inj₂


getOptionsFile : (filepath : string) → string
getOptionsFile fp = combineFileNames (dot-cedille-directory fp) options-file-name

findOptionsFile : (filepath : string) → IO (maybe string)
findOptionsFile fp = h fp (pred (length (splitPath fp))) where
  h : string → ℕ → IO (maybe string)
  h fp 0 = return nothing
  h fp (suc n) =
    let fpc = getOptionsFile fp in
    doesFileExist fpc >>= λ where
      ff → h (takeDirectory fp) n
      tt → return (just fpc)

readOptions : IO (string × cedille-options.options)
readOptions =
  getCurrentDirectory >>=
  canonicalizePath >>=
  findOptionsFile >>= λ where
    nothing →
      getHomeDirectory >>=
      canonicalizePath >>= λ home →
      createOptionsFile (dot-cedille-directory home) >>r
      dot-cedille-directory home , cedille-options.default-options
    (just fp) → readFiniteFile fp >>= λ fc →
      processOptions fp fc >>= λ where
        (inj₁ err) →
          putStrLn (global-error-string err) >>r
          fp , cedille-options.default-options
        (inj₂ ops) → return (fp , ops)


module main-with-options
  (compileTime : UTC)
  (options-filepath : filepath)
  (options : cedille-options.options) where

  open import ctxt
  open import monad-instances
  open import process-cmd options {IO}
  open import parser
  open import spans options {IO}
  open import syntax-util
  open import to-string options
  open import toplevel-state options {IO}
  import interactive-cmds
  open import rkt options
  open import elaboration options
  

  logFilepath : IO filepath
  logFilepath = getHomeDirectory >>=r λ home →
                combineFileNames (dot-cedille-directory home) "log"

  maybeClearLogFile : IO ⊤
  maybeClearLogFile = if cedille-options.options.generate-logs options then
      logFilepath >>= clearFile
    else
      return triv

  logRope : rope → IO ⊤
  logRope s with cedille-options.options.generate-logs options
  ...| ff = return triv
  ...| tt = getCurrentTime >>= λ time →
            logFilepath >>= λ fn →
            withFile fn AppendMode λ hdl →
              hPutRope hdl ([[ "([" ^ utcToString time ^ "] " ]] ⊹⊹ s ⊹⊹ [[ ")\n" ]])

  logMsg : (message : string) → IO ⊤
  logMsg msg = logRope [[ msg ]]

  sendProgressUpdate : string → IO ⊤
  sendProgressUpdate msg = putStr "progress: " >> putStr msg >> putStr "\n"

  progressUpdate : (filename : string) → (do-check : 𝔹) → IO ⊤
  progressUpdate filename do-check =
    sendProgressUpdate ((if do-check then "Checking " else "Skipping ") ^ filename)

  fileBaseName : filepath → string
  fileBaseName fn = base-filename (takeFileName fn)

  {-------------------------------------------------------------------------------
    .cede support
  -------------------------------------------------------------------------------}

  cede-suffix = ".cede"
  rkt-suffix = ".rkt"

  ced-aux-filename : (suffix ced-path : filepath) → filepath
  ced-aux-filename sfx ced-path = 
    let dir = takeDirectory ced-path in
      combineFileNames (dot-cedille-directory dir) (fileBaseName ced-path ^ sfx)

  cede-filename = ced-aux-filename cede-suffix
  rkt-filename = ced-aux-filename rkt-suffix

  maybe-write-aux-file : include-elt → (create-dot-ced-if-missing : IO ⊤) → (filename file-suffix : filepath) → (cedille-options.options → 𝔹) → (include-elt → 𝔹) → rope → IO ⊤
  maybe-write-aux-file ie mk-dot-ced fn sfx f f' r with f options && ~ f' ie
  ...| ff = return triv
  ...| tt = mk-dot-ced >>
            logMsg ("Starting writing " ^ sfx ^ " file " ^ fn) >>
            writeRopeToFile fn r >>
            logMsg ("Finished writing " ^ sfx ^ " file " ^ fn)

  write-aux-files : toplevel-state → filepath → IO ⊤
  write-aux-files s filename with get-include-elt-if s filename
  ...| nothing = return triv
  ...| just ie =
    let dot-ced = createDirectoryIfMissing ff (dot-cedille-directory (takeDirectory filename)) in
    maybe-write-aux-file ie dot-ced (cede-filename filename) cede-suffix
      cedille-options.options.use-cede-files
      include-elt.cede-up-to-date
      ((if include-elt.err ie then [[ "e" ]] else [[]]) ⊹⊹ include-elt-spans-to-rope ie) >>
    maybe-write-aux-file ie dot-ced (rkt-filename filename) rkt-suffix
      cedille-options.options.make-rkt-files
      include-elt.rkt-up-to-date
      (to-rkt-file filename (toplevel-state.Γ s) ie rkt-filename)

  -- we assume the cede file is known to exist at this point
  read-cede-file : (ced-path : filepath) → IO (𝔹 × string)
  read-cede-file ced-path =
    let cede = cede-filename ced-path in
    logMsg ("Started reading .cede file " ^ cede) >>
    get-file-contents cede >>= finish >≯
    logMsg ("Finished reading .cede file " ^ cede)
    where finish : maybe string → IO (𝔹 × string)
          finish nothing = return (tt , global-error-string ("Could not read the file " ^ cede-filename ced-path ^ "."))
          finish (just ss) with string-to-𝕃char ss
          finish (just ss)  | ('e' :: ss') = forceFileRead ss >>r tt , 𝕃char-to-string ss'
          finish (just ss) | _ = forceFileRead ss >>r ff , ss

  add-cedille-extension : string → string
  add-cedille-extension x = x ^ "." ^ cedille-extension

  -- Allows you to say "import FOO.BAR.BAZ" rather than "import FOO/BAR/BAZ"
  replace-dots : filepath → filepath
  replace-dots s = 𝕃char-to-string (h (string-to-𝕃char s)) where
    h : 𝕃 char → 𝕃 char
    h ('.' :: '.' :: cs) = '.' :: '.' :: h cs
    h ('.' :: cs) = pathSeparator :: h cs
    h (c :: cs) = c :: h cs
    h [] = []
  
  find-imported-file : (dirs : 𝕃 filepath) → (unit-name : string) → IO (maybe filepath)
  find-imported-file [] unit-name = return nothing
  find-imported-file (dir :: dirs) unit-name =
      let e = combineFileNames dir (add-cedille-extension unit-name) in
      doesFileExist e >>= λ where
        ff → find-imported-file dirs unit-name
        tt → canonicalizePath e >>=r just

  find-imported-files : (dirs : 𝕃 filepath) → (imports : 𝕃 string) → IO (𝕃 (string × filepath))
  find-imported-files dirs (u :: us) =
    find-imported-file dirs (replace-dots u) >>= λ where
      nothing → logMsg ("Error finding file: " ^ replace-dots u) >> find-imported-files dirs us
      (just fp) → logMsg ("Found import: " ^ fp) >> find-imported-files dirs us >>=r (u , fp) ::_
  find-imported-files dirs [] = return []

  {- new parser test integration -}
  reparse : toplevel-state → filepath → IO toplevel-state
  reparse st filename = 
     doesFileExist filename >>= λ b → 
       (if b then
           (readFiniteFile filename >>= λ s → getCurrentTime >>= λ time → processText s >>=r λ ie → set-last-parse-time-include-elt ie time)
        else return (error-include-elt ("The file " ^ filename ^ " could not be opened for reading.")))
       >>=r set-include-elt st filename
    where processText : string → IO include-elt
          processText x with parseStart x
          processText x | Left (Left cs)  = return (error-span-include-elt ("Error in file " ^ filename ^ ".") "Lexical error." cs)
          processText x | Left (Right cs) = return (error-span-include-elt ("Error in file " ^ filename ^ ".") "Parsing error." cs)        
          processText x | Right t  with cws-types.scanComments x 
          processText x | Right t | t2 = find-imported-files (fst (cedille-options.include-path-insert (takeDirectory filename) (toplevel-state.include-path st)))
                                                             (get-imports t) >>= λ deps →
                                         logMsg ("deps for file " ^ filename ^ ": " ^ 𝕃-to-string (λ {(a , b) → "short: " ^ a ^ ", long: " ^ b}) ", " deps) >>r
                                         new-include-elt filename deps t t2 nothing

  reparse-file : filepath → toplevel-state → IO toplevel-state
  reparse-file filename s =
    reparse s filename >>=r λ s →
    set-include-elt s filename
      (set-cede-file-up-to-date-include-elt
        (set-do-type-check-include-elt
          (get-include-elt s filename) tt) ff)
  
  infixl 1 _&&>>_
  _&&>>_ : IO 𝔹 → IO 𝔹 → IO 𝔹
  (a &&>> b) = a >>= λ a → if a then b else return ff

  aux-up-to-date : filepath → toplevel-state → IO toplevel-state
  aux-up-to-date filename s =
    let rkt = rkt-filename filename in
    doesFileExist rkt &&>> fileIsOlder filename rkt >>=r
    (set-include-elt s filename ∘  (set-rkt-file-up-to-date-include-elt (get-include-elt s filename)))

  ie-up-to-date : filepath → include-elt → IO 𝔹
  ie-up-to-date filename ie =
    getModificationTime filename >>=r λ mt →
    maybe-else ff (λ lpt → lpt utc-after mt) (include-elt.last-parse-time ie)

  import-changed : toplevel-state → filepath → (import-file : string) → IO 𝔹
  import-changed s filename import-file =
    let dtc = include-elt.do-type-check (get-include-elt s import-file)
        cede = cede-filename filename
        cede' = cede-filename import-file in
    case cedille-options.options.use-cede-files options of λ where
      ff → return dtc
      tt → doesFileExist cede &&>> doesFileExist cede' >>= λ where
        ff → return ff
        tt → fileIsOlder cede cede' >>=r λ fio → dtc || fio
   
  any-imports-changed : toplevel-state → filepath → (imports : 𝕃 string) → IO 𝔹
  any-imports-changed s filename [] = return ff
  any-imports-changed s filename (h :: t) =
    import-changed s filename h >>= λ where
      tt → return tt
      ff → any-imports-changed s filename t
  
  file-after-compile : filepath → IO 𝔹
  file-after-compile fn =
    getModificationTime fn >>= λ mt →
    case mt utc-after compileTime of λ where
      tt → doesFileExist options-filepath &&>> fileIsOlder options-filepath fn
      ff → return ff

  ensure-ast-depsh : filepath → toplevel-state → IO toplevel-state
  ensure-ast-depsh filename s with get-include-elt-if s filename
  ...| just ie = ie-up-to-date filename ie >>= λ where
    ff → reparse-file filename s
    tt → return s
  ...| nothing =
      let cede = cede-filename filename in
      return (cedille-options.options.use-cede-files options) &&>>
      doesFileExist cede &&>>
      fileIsOlder filename cede &&>>
      file-after-compile cede >>= λ where
         ff → reparse-file filename s
         tt → reparse s filename >>= λ s →
              read-cede-file filename >>= λ where
                (err , ss) → return
                  (set-include-elt s filename
                  (set-do-type-check-include-elt
                  (set-need-to-add-symbols-to-context-include-elt
                  (set-spans-string-include-elt
                  (get-include-elt s filename) err ss) tt) ff))

  {- helper function for update-asts, which keeps track of the files we have seen so
     we avoid importing the same file twice, and also avoid following cycles in the import
     graph. -}
  {-# TERMINATING #-}
  update-astsh : stringset {- seen already -} → toplevel-state → filepath →
                 IO (stringset {- seen already -} × toplevel-state)
  update-astsh seen s filename = 
    if stringset-contains seen filename then return (seen , s)
    else (ensure-ast-depsh filename s >>= aux-up-to-date filename >>= cont (stringset-insert seen filename))
    where cont : stringset → toplevel-state → IO (stringset × toplevel-state)
          cont seen s with get-include-elt s filename
          cont seen s | ie with include-elt.deps ie
          cont seen s | ie | ds = 
            proc seen s ds
            where proc : stringset → toplevel-state → 𝕃 string → IO (stringset × toplevel-state)
                  proc seen s [] = any-imports-changed s filename ds >>=r λ changed →
                    seen , set-include-elt s filename (set-do-type-check-include-elt ie (include-elt.do-type-check ie || changed))
                  proc seen s (d :: ds) = update-astsh seen s d >>= λ p → 
                                          proc (fst p) (snd p) ds

  {- this function updates the ast associated with the given filename in the toplevel state.
     So if we do not have an up-to-date .cede file (i.e., there is no such file at all,
     or it is older than the given file), reparse the file.  We do this recursively for all
     dependencies (i.e., imports) of the file. -}
  update-asts : toplevel-state → filepath → IO toplevel-state
  update-asts s filename = update-astsh empty-stringset s filename >>=r snd

  log-files-to-check : toplevel-state → IO ⊤
  log-files-to-check s = logRope ([[ "\n" ]] ⊹⊹ (h (trie-mappings (toplevel-state.is s)))) where
    h : 𝕃 (string × include-elt) → rope
    h [] = [[]]
    h ((fn , ie) :: t) = [[ "file: " ]] ⊹⊹ [[ fn ]] ⊹⊹ [[ "\nadd-symbols: " ]] ⊹⊹ [[ 𝔹-to-string (include-elt.need-to-add-symbols-to-context ie) ]] ⊹⊹ [[ "\ndo-type-check: " ]] ⊹⊹ [[ 𝔹-to-string (include-elt.do-type-check ie) ]] ⊹⊹ [[ "\n\n" ]] ⊹⊹ h t

  {- this function checks the given file (if necessary), updates .cede and .rkt files (again, if necessary), and replies on stdout if appropriate -}
  checkFile : toplevel-state → filepath → (should-print-spans : 𝔹) → IO toplevel-state
  checkFile s filename should-print-spans = 
    update-asts s filename >>= λ s →
    log-files-to-check s >>
    logMsg (𝕃-to-string (λ {(im , fn) → "im: " ^ im ^ ", fn: " ^ fn}) "; " (trie-mappings (include-elt.import-to-dep (get-include-elt s filename)))) >>
    process-file progressUpdate s filename (fileBaseName filename) >>= finish
    where
          reply : toplevel-state → IO ⊤
          reply s with get-include-elt-if s filename
          reply s | nothing = putStrLn (global-error-string ("Internal error looking up information for file " ^ filename ^ "."))
          reply s | just ie =
             if should-print-spans then
               putRopeLn (include-elt-spans-to-rope ie)
             else return triv
          finish : toplevel-state × mod-info → IO toplevel-state
          finish (s @ (mk-toplevel-state ip mod is Γ) , ret-mod) =
            logMsg ("Started reply for file " ^ filename) >> -- Lazy, so checking has not been calculated yet?
            reply s >>
            logMsg ("Finished reply for file " ^ filename) >>
            logMsg ("Files with updated spans:\n" ^ 𝕃-to-string (λ x → x) "\n" mod) >>
            let Γ = ctxt-set-current-mod Γ ret-mod in
            writeo mod >>r -- Should process-file now always add files to the list of modified ones because now the cede-/rkt-up-to-date fields take care of whether to rewrite them?
            mk-toplevel-state ip mod is Γ
              where
                writeo : 𝕃 string → IO ⊤
                writeo [] = return triv
                writeo (f :: us) =
                  writeo us >>
                  -- let ie = get-include-elt s f in
                  write-aux-files s f
                  --  (if cedille-options.options.make-rkt-files options && ~ include-elt.rkt-up-to-date ie then (write-rkt-file f (toplevel-state.Γ s) ie rkt-filename) else return triv)

  -- this is the function that handles requests (from the frontend) on standard input
  {-# TERMINATING #-}
  readCommandsFromFrontend : toplevel-state → IO ⊤
  readCommandsFromFrontend s =
      getLine >>= λ input →
      logMsg ("Frontend input: " ^ input) >>
      let input-list : 𝕃 string 
          input-list = (string-split (undo-escape-string input) delimiter) 
              in (handleCommands input-list s) >>= λ s →
          readCommandsFromFrontend s
          where
              delimiter : char
              delimiter = '§'

              errorCommand : 𝕃 string → toplevel-state → IO ⊤
              errorCommand ls s = putStrLn (global-error-string "Invalid command sequence \\\\\"" ^ (𝕃-to-string (λ x → x) ", " ls) ^ "\\\\\".")

              debugCommand : toplevel-state → IO ⊤
              debugCommand s = putStrLn (escape-string (toplevel-state-to-string s))

              checkCommand : 𝕃 string → toplevel-state → IO toplevel-state
              checkCommand (input :: []) s = canonicalizePath input >>= λ input-filename →
                          checkFile (set-include-path s (cedille-options.include-path-insert (takeDirectory input-filename) (toplevel-state.include-path s)))
                          input-filename tt {- should-print-spans -}
              checkCommand ls s = errorCommand ls s >>r s

    {-          findCommand : 𝕃 string → toplevel-state → IO toplevel-state
              findCommand (symbol :: []) s = putStrLn (find-symbols-to-JSON symbol (toplevel-state-lookup-occurrences symbol s)) >>= λ x → return s
              findCommand _ s = errorCommand s -}

              handleCommands : 𝕃 string → toplevel-state → IO toplevel-state
              handleCommands ("progress stub" :: xs) = return
              handleCommands ("status ping" :: xs) s = putStrLn "idle" >> return s
              handleCommands ("check" :: xs) s = checkCommand xs s
              handleCommands ("debug" :: []) s = debugCommand s >>r s
              handleCommands ("elaborate" :: x :: x' :: []) s = elab-all s x x' >>r s
              handleCommands ("interactive" :: xs) s = interactive-cmds.interactive-cmd options xs s >>r s
  --            handleCommands ("find" :: xs) s = findCommand xs s
              handleCommands xs s = errorCommand xs s >>r s


  -- function to process command-line arguments
  processArgs : 𝕃 string → IO ⊤ 

  -- this is the case for when we are called with a single command-line argument, the name of the file to process
  processArgs (input-filename :: []) =
    canonicalizePath input-filename >>= λ input-filename → 
    checkFile (new-toplevel-state (cedille-options.include-path-insert (takeDirectory input-filename) (cedille-options.options.include-path options)))
      input-filename ff {- should-print-spans -} >>= finish input-filename
    where finish : string → toplevel-state → IO ⊤
          finish input-filename s = return triv
{-            let ie = get-include-elt s input-filename in
            if include-elt.err ie then (putRopeLn (include-elt-spans-to-rope ie)) else return triv
-}
  -- this is the case where we will go into a loop reading commands from stdin, from the fronted
  processArgs [] = readCommandsFromFrontend (new-toplevel-state (cedille-options.options.include-path options))

  -- all other cases are errors
  processArgs xs = putStrLn ("Run with the name of one file to process, or run with no command-line arguments and enter the\n"
                           ^ "names of files one at a time followed by newlines (this is for the emacs mode).")
  
  main' : IO ⊤
  main' =
    maybeClearLogFile >>
    logMsg ("Started Cedille process (compiled at: " ^ utcToString compileTime ^ ")") >>
    getArgs >>=
    processArgs

postulate
  initializeStdinToUTF8 : IO ⊤
  setStdinNewlineMode : IO ⊤
  compileTime : UTC

{-# FOREIGN GHC {-# LANGUAGE TemplateHaskell #-} #-}
{-# FOREIGN GHC import qualified System.IO #-}
{-# FOREIGN GHC import qualified Data.Time.Clock #-}
{-# FOREIGN GHC import qualified Data.Time.Format #-}
{-# FOREIGN GHC import qualified Data.Time.Clock.POSIX #-}
{-# FOREIGN GHC import qualified Language.Haskell.TH.Syntax #-}
{-# COMPILE GHC initializeStdinToUTF8 = System.IO.hSetEncoding System.IO.stdin System.IO.utf8 #-}
{-# COMPILE GHC setStdinNewlineMode = System.IO.hSetNewlineMode System.IO.stdin System.IO.universalNewlineMode #-}
{-# COMPILE GHC compileTime =
  maybe (Data.Time.Clock.POSIX.posixSecondsToUTCTime (fromIntegral 0)) id
  (Data.Time.Format.parseTimeM True Data.Time.Format.defaultTimeLocale "%s"
    $(Language.Haskell.TH.Syntax.runIO
      (Data.Time.Clock.getCurrentTime >>= \ t ->
       return (Language.Haskell.TH.Syntax.LitE
         (Language.Haskell.TH.Syntax.StringL
           (Data.Time.Format.formatTime Data.Time.Format.defaultTimeLocale "%s" t)))))
    :: Maybe Data.Time.Clock.UTCTime) #-}

-- main entrypoint for the backend
main : IO ⊤
main = initializeStdoutToUTF8 >>
       initializeStdinToUTF8 >>
       setStdoutNewlineMode >>
       setStdinNewlineMode >>
       setToLineBuffering >>
       readOptions >>=
       uncurry (main-with-options.main' compileTime)
