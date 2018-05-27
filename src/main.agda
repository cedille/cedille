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


module main-with-options (options : cedille-options.options) where

  open import ctxt
  open import process-cmd options {IO}
  open import parser
  open import spans options {IO}
  open import syntax-util
  open import to-string options
  open import toplevel-state options {IO}
  import interactive-cmds
  open import rkt options
  open import elaboration options

  logFilepath : IO string
  logFilepath = getHomeDirectory >>= λ home →
                return (combineFileNames (dot-cedille-directory home) "log")

  maybeClearLogFile : IO ⊤
  maybeClearLogFile = if cedille-options.options.generate-logs options then
      logFilepath >>= clearFile
    else
      return triv

  logRope : rope → IO ⊤
  logRope s = if cedille-options.options.generate-logs options then
        (getCurrentTime >>= λ time →
        logFilepath >>= λ fn →
        withFile fn AppendMode (λ hdl →
          hPutRope hdl ([[ "([" ^ utcToString time ^ "] " ]] ⊹⊹ s ⊹⊹ [[ ")\n" ]])))
      else
        return triv

  logMsg : (message : string) → IO ⊤
  logMsg msg = logRope [[ msg ]]

  sendProgressUpdate : string → IO ⊤
  sendProgressUpdate msg = putStr "progress: " >> putStr msg >> putStr "\n"

  progressUpdate : (filename : string) → (do-check : 𝔹) → IO ⊤
  progressUpdate filename do-check =
    sendProgressUpdate ((if do-check then "Checking " else "Skipping ") ^ filename)

  fileBaseName : string → string
  fileBaseName fn = base-filename (takeFileName fn)

  {-------------------------------------------------------------------------------
    .cede support
  -------------------------------------------------------------------------------}

  cede-suffix = ".cede"
  cedc-suffix = ".cedc"

  ced-ec-filename : (suffix ced-path : string) → string
  ced-ec-filename sfx ced-path = 
    let dir = takeDirectory ced-path in
      combineFileNames (dot-cedille-directory dir) (fileBaseName ced-path ^ sfx)

  cede-filename = ced-ec-filename cede-suffix
  cedc-filename = ced-ec-filename cedc-suffix

  maybe-write-aux-file : include-elt → (filename file-suffix : string) → (cedille-options.options → 𝔹) → (include-elt → 𝔹) → rope → IO ⊤
  maybe-write-aux-file ie fn sfx f f' r with f options && ~ f' ie
  ...| ff = return triv
  ...| tt = logMsg ("Starting writing " ^ sfx ^ " file " ^ fn) >>
            writeRopeToFile fn r >>
            logMsg ("Finished writing " ^ sfx ^ " file " ^ fn)

  write-aux-files : toplevel-state → (filename : string) → IO ⊤
  write-aux-files s filename with get-include-elt-if s filename
  ...| nothing = return triv
  ...| just ie =
    createDirectoryIfMissing ff (dot-cedille-directory (takeDirectory filename)) >>
    maybe-write-aux-file ie (cede-filename filename) cede-suffix
      cedille-options.options.use-cede-files
      include-elt.cede-up-to-date
      ((if include-elt.err ie then [[ "e" ]] else [[]]) ⊹⊹ include-elt-spans-to-rope ie) >>
    maybe-write-aux-file ie (cedc-filename filename) cedc-suffix
      cedille-options.options.make-core-files
      include-elt.cedc-up-to-date
      (maybe-else [[ "Elaboration error" ]] id (elab-file s filename))
      -- Maybe merge racket files into this function?

  -- we assume the cede file is known to exist at this point
  read-cede-file : (ced-path : string) → IO (𝔹 × string)
  read-cede-file ced-path =
    let cede = cede-filename ced-path in
    logMsg ("Started reading .cede file " ^ cede) >>
    get-file-contents cede >>= λ c → finish c >>≠
    logMsg ("Finished reading .cede file " ^ cede)
    where finish : maybe string → IO (𝔹 × string)
          finish nothing = return (tt , global-error-string ("Could not read the file " ^ cede-filename ced-path ^ "."))
          finish (just ss) with string-to-𝕃char ss
          finish (just ss)  | ('e' :: ss') = forceFileRead ss >> return (tt , 𝕃char-to-string ss')
          finish (just ss) | _ = forceFileRead ss >> return (ff , ss)

  add-cedille-extension : string → string
  add-cedille-extension x = x ^ "." ^ cedille-extension

  find-imported-file : (dirs : 𝕃 string) → (unit-name : string) → IO (maybe string)
  find-imported-file [] unit-name = return nothing
  find-imported-file (dir :: dirs) unit-name =
      let e = combineFileNames dir (add-cedille-extension unit-name) in
      doesFileExist e >>= λ where
        ff → find-imported-file dirs unit-name
        tt → canonicalizePath e >>= return ∘ just

  -- return a list of pairs (i,p,pn) where i is the import string in the file, p is the full path for that imported file,
  -- and pn is the name to send to the frontend as a progress update while checking/skipping
  find-imported-files : (dirs : 𝕃 string) → (imports : 𝕃 string) → IO (𝕃 (string × string))
  find-imported-files dirs (u :: us) =
    find-imported-file dirs ({-replace-dots-} u) >>= λ where
      nothing → logMsg ("Error finding file: " ^ u) >> find-imported-files dirs us
      (just fp) → logMsg ("Found import: " ^ fp) >> find-imported-files dirs us >>= λ ps → return ((u , fp) :: ps)
  find-imported-files dirs [] = return []

  {- new parser test integration -}
  reparse : toplevel-state → (filename : string) → IO toplevel-state
  reparse st filename = 
     doesFileExist filename >>= λ b → 
       (if b then
           (readFiniteFile filename >>= λ s → getCurrentTime >>= λ time → processText s >>= λ ie → return (set-last-parse-time-include-elt ie time))
        else return (error-include-elt ("The file " ^ filename ^ " could not be opened for reading."))) >>= λ ie →
          return (set-include-elt st filename ie)
    where processText : string → IO include-elt
          processText x with parseStart x
          processText x | Left (Left cs)  = return (error-span-include-elt ("Error in file " ^ filename ^ ".") "Lexical error." cs)
          processText x | Left (Right cs) = return (error-span-include-elt ("Error in file " ^ filename ^ ".") "Parsing error." cs)        
          processText x | Right t  with cws-types.scanComments x 
          processText x | Right t | t2 = find-imported-files (fst (cedille-options.include-path-insert (takeDirectory filename) (toplevel-state.include-path st)))
                                                             (get-imports t) >>= λ deps →
                                         logMsg ("deps for file " ^ filename ^ ": " ^ 𝕃-to-string (λ {(a , b) → "short: " ^ a ^ ", long: " ^ b}) ", " deps) >> return (new-include-elt filename deps t t2 nothing)

  reparse-file : string → toplevel-state → IO toplevel-state
  reparse-file filename s =
    reparse s filename >>= λ s →
    return (set-include-elt s filename
            (set-cede-file-up-to-date-include-elt
             (set-do-type-check-include-elt
              (get-include-elt s filename) tt) ff))
  
  &&>> : IO 𝔹 → IO 𝔹 → IO 𝔹
  &&>> a b = a >>= λ a → if a then b else return ff

  aux-up-to-date : (filename : string) → toplevel-state → IO toplevel-state
  aux-up-to-date filename s =
    let cedc = cedc-filename filename
        rkt = rkt-filename filename in
    &&>> (doesFileExist cedc) (fileIsOlder filename cedc) >>= λ cedc →
    &&>> (doesFileExist rkt) (fileIsOlder filename rkt) >>= λ rkt → return
    (set-include-elt s filename
    (set-cedc-file-up-to-date-include-elt
    (set-rkt-file-up-to-date-include-elt
    (get-include-elt s filename)
    rkt) cedc))

  ie-up-to-date : string → include-elt → IO 𝔹
  ie-up-to-date filename ie =
    getModificationTime filename >>= λ mt →
    return (maybe-else ff (λ lpt → lpt utc-after mt) (include-elt.last-parse-time ie))    

  import-changed : toplevel-state → (filename : string) → (import-file : string) → IO 𝔹
  import-changed s filename import-file =
    let dtc = include-elt.do-type-check (get-include-elt s import-file) in
    let cede = cede-filename filename in
    let cede' = cede-filename import-file in
    case cedille-options.options.use-cede-files options of λ where
      ff → return dtc
      tt → doesFileExist cede >>= λ where
        ff → return ff
        tt → doesFileExist cede' >>= λ where
          ff → return ff
          tt → fileIsOlder cede cede' >>= λ fio → return (dtc || fio)
   
  any-imports-changed : toplevel-state → (filename : string) → (imports : 𝕃 string) → IO 𝔹
  any-imports-changed s filename [] = return ff
  any-imports-changed s filename (h :: t) = import-changed s filename h >>= λ where
    tt → return tt
    ff → any-imports-changed s filename t

  ensure-ast-depsh : string → toplevel-state → IO toplevel-state
  ensure-ast-depsh filename s with get-include-elt-if s filename
  ...| just ie = ie-up-to-date filename ie >>= λ where
    ff → reparse-file filename s
    tt → return s
  ...| nothing = case cedille-options.options.use-cede-files options of λ where
    ff → reparse-file filename s
    tt →
      let cede = cede-filename filename in
      doesFileExist cede >>= λ where
        ff → reparse-file filename s
        tt → fileIsOlder filename cede >>= λ where
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
  update-astsh : stringset {- seen already -} → toplevel-state → (filename : string) →
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
                  proc seen s [] = any-imports-changed s filename ds >>= λ changed →
                    let dtc = include-elt.do-type-check ie || changed in
                    return (seen , set-include-elt s filename (set-do-type-check-include-elt ie dtc))
                  proc seen s (d :: ds) = update-astsh seen s d >>= λ p → 
                                          proc (fst p) (snd p) ds

  {- this function updates the ast associated with the given filename in the toplevel state.
     So if we do not have an up-to-date .cede file (i.e., there is no such file at all,
     or it is older than the given file), reparse the file.  We do this recursively for all
     dependencies (i.e., imports) of the file. -}
  update-asts : toplevel-state → (filename : string) → IO toplevel-state
  update-asts s filename = update-astsh empty-stringset s filename >>= λ p → 
    return (snd p)

  log-files-to-check : toplevel-state → IO ⊤
  log-files-to-check s = logRope ([[ "\n" ]] ⊹⊹ (h (trie-mappings (toplevel-state.is s)))) where
    h : 𝕃 (string × include-elt) → rope
    h [] = [[]]
    h ((fn , ie) :: t) = [[ "file: " ]] ⊹⊹ [[ fn ]] ⊹⊹ [[ "\nadd-symbols: " ]] ⊹⊹ [[ 𝔹-to-string (include-elt.need-to-add-symbols-to-context ie) ]] ⊹⊹ [[ "\ndo-type-check: " ]] ⊹⊹ [[ 𝔹-to-string (include-elt.do-type-check ie) ]] ⊹⊹ [[ "\n\n" ]] ⊹⊹ h t

  {- this function checks the given file (if necessary), updates .cede and .rkt files (again, if necessary), and replies on stdout if appropriate -}
  checkFile : toplevel-state → (filename : string) → (should-print-spans : 𝔹) → IO toplevel-state
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
            writeo mod >> -- Should process-file now always add files to the list of modified ones because now the cede-/rkt-up-to-date fields take care of whether to rewrite them?
            return (mk-toplevel-state ip mod is Γ)
              where
                writeo : 𝕃 string → IO ⊤
                writeo [] = return triv
                writeo (f :: us) =
                  writeo us >>
                  let ie = get-include-elt s f in
                  write-aux-files s f >> -- (record s {Γ = Γ}) f >>
                  --  (if cedille-options.options.use-cede-files options && ~ include-elt.cede-up-to-date ie then (write-cede-file Γ f ie) else return triv) >>
                    (if cedille-options.options.make-rkt-files options && ~ include-elt.rkt-up-to-date ie then (write-rkt-file f (toplevel-state.Γ s) ie) else return triv)

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
              checkCommand ls s = errorCommand ls s >> return s

    {-          findCommand : 𝕃 string → toplevel-state → IO toplevel-state
              findCommand (symbol :: []) s = putStrLn (find-symbols-to-JSON symbol (toplevel-state-lookup-occurrences symbol s)) >>= λ x → return s
              findCommand _ s = errorCommand s -}

              handleCommands : 𝕃 string → toplevel-state → IO toplevel-state
              handleCommands ("progress stub" :: xs) = return
              handleCommands ("check" :: xs) s = checkCommand xs s
              handleCommands ("debug" :: []) s = debugCommand s >> return s
              handleCommands ("elaborate" :: x :: x' :: []) s = elab-all s x x' >> return s
              handleCommands ("interactive" :: xs) s = interactive-cmds.interactive-cmd options xs s >> return s
  --            handleCommands ("find" :: xs) s = findCommand xs s
              handleCommands xs s = errorCommand xs s >> return s


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
    logMsg "Started Cedille process" >>
    getArgs >>=
    processArgs

createOptionsFile : (options-filepath : string) → IO ⊤
createOptionsFile ops-fp = withFile ops-fp WriteMode (λ hdl →
  hPutRope hdl (cedille-options.options-to-rope cedille-options.default-options))

str-bool-to-𝔹 : options-types.str-bool → 𝔹
str-bool-to-𝔹 options-types.StrBoolTrue = tt
str-bool-to-𝔹 options-types.StrBoolFalse = ff

opts-to-options : options-types.opts → cedille-options.options
opts-to-options (options-types.OptsCons (options-types.Lib fps) ops) =
  record (opts-to-options ops) { include-path = paths-to-stringset fps }
  where paths-to-stringset : options-types.paths → 𝕃 string × stringset
        paths-to-stringset (options-types.PathsCons fp fps) =
          cedille-options.include-path-insert fp (paths-to-stringset fps)
        paths-to-stringset options-types.PathsNil = [] , empty-stringset
opts-to-options (options-types.OptsCons (options-types.UseCedeFiles b) ops) =
  record (opts-to-options ops) { use-cede-files = str-bool-to-𝔹 b }
opts-to-options (options-types.OptsCons (options-types.MakeRktFiles b) ops) =
  record (opts-to-options ops) { make-rkt-files = str-bool-to-𝔹 b }
opts-to-options (options-types.OptsCons (options-types.GenerateLogs b) ops) =
  record (opts-to-options ops) { generate-logs = str-bool-to-𝔹 b }
opts-to-options (options-types.OptsCons (options-types.ShowQualifiedVars b) ops) =
  record (opts-to-options ops) { show-qualified-vars = str-bool-to-𝔹 b }
opts-to-options (options-types.OptsCons (options-types.MakeCoreFiles b) ops) =
  record (opts-to-options ops) { make-core-files = str-bool-to-𝔹 b }
opts-to-options options-types.OptsNil = cedille-options.default-options

-- helper function to try to parse the options file
processOptions : string → string → (string ⊎ cedille-options.options)
processOptions filename s with options-types.scanOptions s
...                           | options-types.Left cs = inj₁ ("Parse error in file " ^ filename ^ " " ^ cs ^ ".")
...                           | options-types.Right (options-types.File oo) = inj₂ (opts-to-options oo)

-- read the ~/.cedille/options file
readOptions : IO cedille-options.options
readOptions =
  getHomeDirectory >>= λ homedir →
    let homecedir = dot-cedille-directory homedir in
    let optsfile = combineFileNames homecedir options-file-name in
      createDirectoryIfMissing ff homecedir >>
      doesFileExist optsfile >>= λ b → 
       if b then
         (readFiniteFile optsfile >>= λ f →
         case (processOptions optsfile f) of λ where
           (inj₁ err) → putStrLn (global-error-string err) >>
                        return cedille-options.default-options
           (inj₂ ops) → return ops)
       else
         (createOptionsFile optsfile >>
         return cedille-options.default-options)

postulate
  initializeStdinToUTF8 : IO ⊤
  setStdinNewlineMode : IO ⊤
{-# COMPILED initializeStdinToUTF8  System.IO.hSetEncoding System.IO.stdin System.IO.utf8 #-}
{-# COMPILED setStdinNewlineMode System.IO.hSetNewlineMode System.IO.stdin System.IO.universalNewlineMode #-}

-- main entrypoint for the backend
main : IO ⊤
main = initializeStdoutToUTF8 >>
       initializeStdinToUTF8 >>
       setStdoutNewlineMode >>
       setStdinNewlineMode >>
       setToLineBuffering >>
       readOptions >>=
       main-with-options.main'
