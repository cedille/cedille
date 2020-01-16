module main where

import string-format
-- for parser for Cedille 
open import cedille-types

-- for parser for options files
import options-types
import cedille-options

-- for parser for Cedille comments & whitespace
import cws-types

import io
open import constants
open import general-util
open import json

record cedille-args : Set where
  constructor mk-cedille-args
  field
    opts-file : maybe filepath
    file-to-process : maybe filepath
    about     : 𝔹
    help      : 𝔹
    do-elab   : maybe filepath
    confirm-read-stdin : 𝔹

default-cedille-args =
  record { opts-file = nothing ;
           file-to-process = nothing ;
           about = ff ;
           help = ff ;
           do-elab = nothing ;
           confirm-read-stdin = ff}

-- get $HOME/.cedille, creating it if it does not exist
getHomeCedilleDirectory : IO filepath
getHomeCedilleDirectory =
  getHomeDirectory >>= λ home →
  let d = dot-cedille-directory home in
    io.createDirectoryIfMissing ff d >>
    return d

postulate
  initializeStdinToUTF8 : IO ⊤
  setStdinNewlineMode : IO ⊤
  compileTime : UTC
  templatesDir : filepath
  die : {A : Set} → 𝕃 char → IO A

{-# FOREIGN GHC {-# LANGUAGE TemplateHaskell #-} #-}
{-# FOREIGN GHC import qualified System.IO #-}
{-# FOREIGN GHC import qualified System.Exit #-}
{-# FOREIGN GHC import qualified Data.Time.Clock #-}
{-# FOREIGN GHC import qualified Data.Time.Format #-}
{-# FOREIGN GHC import qualified Data.Time.Clock.POSIX #-}
{-# FOREIGN GHC import qualified Language.Haskell.TH.Syntax #-}
{-# COMPILE GHC die = \ _ -> System.Exit.die #-}
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

say-about : filepath → IO ⊤
say-about optfp =
   putStrLn $ "Compiled:     " ^ (utcToString compileTime) ^ "\n" ^
              "Options file: " ^ optfp ^ "\n"

createOptionsFile : (dot-ced-dir : string) → IO ⊤
createOptionsFile dot-ced-dir =
  let ops-fp = combineFileNames dot-ced-dir options-file-name in
  createDirectoryIfMissing ff (takeDirectory ops-fp) >>
  withFile ops-fp WriteMode (flip hPutRope (cedille-options.options-to-rope cedille-options.default-options))

options-absolute-path : (options-fp some-fp : filepath) → IO filepath
options-absolute-path ofp fp =
  (filepath-replace-tilde fp >>= flip maybe-else return
    (doesFileExist fp >>=r λ fpₑ →
      if fpₑ then fp else combineFileNames (takeDirectory (takeDirectory ofp)) fp))
  >>= canonicalizePath

opts-to-options : filepath → options-types.opts → IO cedille-options.options
opts-to-options ofp (options-types.OptsCons (options-types.Lib fps) ops) =
  opts-to-options ofp ops >>= λ ops → paths-to-stringset fps >>=r λ ip → record ops { include-path = ip }
  where paths-to-stringset : options-types.paths → IO (𝕃 string × stringset)
        paths-to-stringset (options-types.PathsCons fp fps) =
          let rfp = combineFileNames (takeDirectory (takeDirectory ofp)) fp in
          paths-to-stringset fps >>= λ ps →
          doesDirectoryExist rfp >>= λ rfpₑ →
          doesDirectoryExist fp >>= λ fpₑ →
          (if rfpₑ
            then (canonicalizePath rfp >>= λ rfp →
                  return (cedille-options.include-path-insert rfp ps))
            else return ps) >>= λ ps →
          if fpₑ
            then (canonicalizePath fp >>= λ fp →
                  return (cedille-options.include-path-insert fp ps))
            else return ps
        paths-to-stringset options-types.PathsNil = return ([] , empty-stringset)
opts-to-options ofp (options-types.OptsCons (options-types.UseCedeFiles b) ops) =
  opts-to-options ofp ops >>=r λ ops → record ops { use-cede-files = b }
opts-to-options ofp (options-types.OptsCons (options-types.MakeRktFiles b) ops) =
  opts-to-options ofp ops >>=r λ ops → record ops { make-rkt-files = b }
opts-to-options ofp (options-types.OptsCons (options-types.GenerateLogs b) ops) =
  opts-to-options ofp ops >>=r λ ops → record ops { generate-logs = b }
opts-to-options ofp (options-types.OptsCons (options-types.ShowQualifiedVars b) ops) =
  opts-to-options ofp ops >>=r λ ops → record ops { show-qualified-vars = b }
opts-to-options ofp (options-types.OptsCons (options-types.EraseTypes b) ops) =
  opts-to-options ofp ops >>=r λ ops → record ops { erase-types = b }
opts-to-options ofp (options-types.OptsCons (options-types.PrettyPrintColumns b) ops) =
  opts-to-options ofp ops >>=r λ ops → record ops { pretty-print-columns = string-to-ℕ0 b }
opts-to-options ofp (options-types.OptsCons (options-types.DatatypeEncoding fp?) ops) =
  maybe-map (options-absolute-path ofp) fp? >>=? λ fp? →
  opts-to-options ofp ops >>=r λ ops → record ops { datatype-encoding = (_, nothing) <$> fp? }
opts-to-options ofp options-types.OptsNil = return cedille-options.default-options

-- helper function to try to parse the options file
processOptions : filepath → string → IO (string ⊎ cedille-options.options)
processOptions filename s with options-types.scanOptions s
...| options-types.Left cs = return (inj₁ ("Parse error in file " ^ filename ^ " " ^ cs ^ "."))
...| options-types.Right (options-types.File oo) =
  opts-to-options filename oo
  >>= λ opts → if cedille-options.options.make-rkt-files opts
    then return ∘ inj₁ $ "Racket compilation disabled, please set to false in " ^ filename ^ "."
  else (return ∘ inj₂ $ opts) 


getOptionsFile : (filepath : string) → string
getOptionsFile fp = combineFileNames (dot-cedille-directory fp) options-file-name

findOptionsFile' : (filepath : string) → IO (maybe string)
findOptionsFile' fp =
  traverseParents fp (fp-fuel fp)
  >>= λ where
    fpc?@(just fpc) → return fpc?
    nothing → getHomeDirectory >>= getOptions?

  where
  getOptions? : (filepath : string) → IO ∘ maybe $ string
  getOptions? fp =
    let fpc = getOptionsFile fp in
    doesFileExist fpc >>= λ where
      ff → return nothing
      tt → return ∘ just $ fpc

  traverseParents : string → ℕ → IO (maybe string)
  traverseParents fp 0 = return nothing
  traverseParents fp (suc n) =
    getOptions? fp >>= λ where
      nothing → traverseParents (takeDirectory fp) n
      fpc?@(just fpc) → return fpc?

  fp-fuel : (filepath : string) → ℕ
  fp-fuel fp = pred ∘' length ∘' splitPath $ fp

findOptionsFile : IO (maybe string)
findOptionsFile =
  (getCurrentDirectory >>= canonicalizePath) >>= findOptionsFile'

readOptions : maybe filepath → IO (filepath × cedille-options.options)
readOptions nothing =
  getHomeCedilleDirectory >>= λ home →
  createOptionsFile home >>r
  dot-cedille-directory home , cedille-options.default-options
readOptions (just fp) = readFiniteFile fp >>= λ fc →
  processOptions fp fc >>= λ where
    (inj₁ err) →
      putStrLn (global-error-string err) >>r
        fp , cedille-options.default-options
    (inj₂ ops) → return (fp , ops)

showCedilleUsage : IO ⊤
showCedilleUsage =
    putStrLn ("Command-line usage: cedille [--e elab-dir | --options options-file | --about ] file-to-check\n"
            ^ "With no arguments, read commands from the front-end on stdin.")


module main-with-options
  (compileTime : UTC)
  (options-filepath : filepath)
  (options : cedille-options.options)
  (die : {A : Set} → 𝕃 char → IO A) where

  open import ctxt
  --open import instances
  open import process-cmd options {IO}
  open import parser
  open import spans options {IO}
  open import syntax-util
  open import to-string options
  open import toplevel-state options {IO}
  open import interactive-cmds options
  open import rkt options
  open import elab-util options
  open import communication-util options
  
  logFilePathIO : IO filepath
  logFilePathIO = getHomeCedilleDirectory >>=r (flip combineFileNames $ "log")

  maybeClearLogFile : IO filepath
  maybeClearLogFile =
    logFilePathIO >>=
      λ logFilePath →
        ifM (cedille-options.options.generate-logs options) (clearFile logFilePath) >>
        return logFilePath

  fileBaseName : filepath → string
  fileBaseName fn = base-filename (takeFileName fn)

  fileSuffix : filepath → string
  fileSuffix = maybe-else cedille-extension id ∘ var-suffix

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

  maybe-write-aux-file : toplevel-state → include-elt → (create-dot-ced-if-missing : IO ⊤) →
                         (filename file-suffix : filepath) → (cedille-options.options → 𝔹) → (include-elt → 𝔹) → rope → IO ⊤
  maybe-write-aux-file s ie mk-dot-ced fn sfx f f' r with f options && ~ f' ie
  ...| ff = return triv
  ...| tt = mk-dot-ced >>
            logMsg s ("Starting writing " ^ sfx ^ " file " ^ fn) >>
            writeRopeToFile fn r >>
            logMsg s ("Finished writing " ^ sfx ^ " file " ^ fn)

  write-aux-files : toplevel-state → filepath → IO ⊤
  write-aux-files s filename with get-include-elt-if s filename
  ...| nothing = return triv
  ...| just ie =
    let dot-ced = createDirectoryIfMissing ff (dot-cedille-directory (takeDirectory filename)) in
    maybe-write-aux-file s ie dot-ced (cede-filename filename) cede-suffix
      cedille-options.options.use-cede-files
      include-elt.cede-up-to-date
      ((if include-elt.err ie then [[ "e" ]] else [[]]) ⊹⊹ json-to-rope (include-elt-spans-to-json ie)) >>
    maybe-write-aux-file s ie dot-ced (rkt-filename filename) rkt-suffix
      cedille-options.options.make-rkt-files
      include-elt.rkt-up-to-date
      (to-rkt-file filename (toplevel-state.Γ s) ie rkt-filename)

  -- we assume the cede file is known to exist at this point
  read-cede-file : toplevel-state → (ced-path : filepath) → IO (𝔹 × string)
  read-cede-file s ced-path =
    let cede = cede-filename ced-path in
    logMsg s ("Started reading .cede file " ^ cede) >>
    (get-file-contents cede >>= finish) >≯
    logMsg s ("Finished reading .cede file " ^ cede)
    where finish : maybe string → IO (𝔹 × string)
          finish nothing = return (tt , global-error-string ("Could not read the file " ^ cede-filename ced-path ^ "."))
          finish (just ss) with string-to-𝕃char ss
          finish (just ss)  | ('e' :: ss') = forceFileRead ss >>r tt , 𝕃char-to-string ss'
          finish (just ss) | _ = forceFileRead ss >>r ff , ss

  --add-cedille-extension : string → string
  --add-cedille-extension x = x ^ "." ^ cedille-extension

  --add-cdle-extension : string → string
  --add-cdle-extension x = x ^ "." ^ cdle-extension

  -- Allows you to say "import FOO.BAR.BAZ" rather than "import FOO/BAR/BAZ"
  replace-dots : filepath → filepath
  replace-dots s = 𝕃char-to-string (h (string-to-𝕃char s)) where
    h : 𝕃 char → 𝕃 char
    h ('.' :: '.' :: cs) = '.' :: '.' :: h cs
    h ('.' :: cs) = pathSeparator :: h cs
    h (c :: cs) = c :: h cs
    h [] = []
  
  find-imported-file : (sfx : string) → (dirs : 𝕃 filepath) → (unit-name : string) → IO (maybe filepath)
  find-imported-file sfx [] unit-name = return nothing
  find-imported-file sfx (dir :: dirs) unit-name =
    let e = combineFileNames dir (unit-name ^ "." ^ sfx) in
    doesFileExist e >>= λ where
      tt → canonicalizePath e >>=r just
      ff → find-imported-file sfx dirs unit-name
{-
  find-imported-file sfx (dir :: dirs) unit-name =
      let e₁ = combineFileNames dir (add-cedille-extension unit-name)
          e₂ = combineFileNames dir (add-cdle-extension unit-name)
          e? = λ e → doesFileExist e >>=r λ e? → ifMaybej e? e in
      (e? e₁ >>= λ e₁ → e? e₂ >>=r λ e₂ → e₁ maybe-or e₂) >>= λ where
        nothing → find-imported-file sfx dirs unit-name
        (just e) → canonicalizePath e >>=r just
-}

  find-imported-files : toplevel-state → (sfx : string) → (dirs : 𝕃 filepath) → (imports : 𝕃 string) → IO (𝕃 (string × filepath))
  find-imported-files s sfx dirs (u :: us) =
    find-imported-file sfx dirs (replace-dots u) >>= λ where
      nothing → logMsg s ("Error finding file: " ^ replace-dots u) >> find-imported-files s sfx dirs us
      (just fp) → logMsg s ("Found import: " ^ fp) >> find-imported-files s sfx dirs us >>=r (u , fp) ::_
  find-imported-files s sfx dirs [] = return []

  get-imports : ex-file → 𝕃 string
  get-imports (ExModule is _ _ mn _ cs _) =
    map (λ {(ExImport _ _ _ x _ _ _) → x}) (is ++ ex-cmds-to-imps cs)

  {- new parser test integration -}
  reparse : toplevel-state → filepath → IO toplevel-state
  reparse st filename =
     doesFileExist filename >>= λ fileExists →
       (if fileExists then
           (readFiniteFile filename >>= λ source →
            getCurrentTime >>= λ time →
            processText source >>= λ ie →
            return (set-last-parse-time-include-elt ie time) >>=r λ ie ->
            set-source-include-elt ie source)
        else return (error-include-elt ("The file " ^ filename ^ " could not be opened for reading.")))
       >>=r set-include-elt st filename
    where processText : string → IO include-elt
          processText x with parseStart x
          processText x | Left (Left cs)  = return (error-span-include-elt ("Error in file " ^ filename ^ ".") "Lexical error." cs)
          processText x | Left (Right cs) = return (error-span-include-elt ("Error in file " ^ filename ^ ".") "Parsing error." cs)        
          processText x | Right t  with cws-types.scanComments x 
          processText x | Right t | t2 =
            find-imported-files st (fileSuffix filename)
              (fst (cedille-options.include-path-insert (takeDirectory filename) (toplevel-state.include-path st)))
              (get-imports t) >>= λ deps →
            logMsg st ("deps for file " ^ filename ^ ": " ^ 𝕃-to-string (λ {(a , b) → "short: " ^ a ^ ", long: " ^ b}) ", " deps) >>r
            new-include-elt filename deps t t2 nothing

  reparse-file : filepath → toplevel-state → IO toplevel-state
  reparse-file filename s =
    reparse s filename >>=r λ s →
    set-include-elt s filename
      (set-cede-file-up-to-date-include-elt
        (set-do-type-check-include-elt
          (get-include-elt s filename) tt) ff)
  
  infixl 2 _&&>>_
  _&&>>_ : IO 𝔹 → IO 𝔹 → IO 𝔹
  (a &&>> b) = a >>= λ a → if a then b else return ff

  aux-up-to-date : filepath → toplevel-state → IO toplevel-state
  aux-up-to-date filename s =
    let rkt = rkt-filename filename in
    (doesFileExist rkt &&>> fileIsOlder filename rkt) >>=r
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
      tt → (doesFileExist cede &&>> doesFileExist cede') >>= λ where
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
      (return (cedille-options.options.use-cede-files options) &&>>
       doesFileExist cede &&>>
       fileIsOlder filename cede &&>>
       file-after-compile cede) >>= λ where
         ff → reparse-file filename s
         tt → reparse s filename >>= λ s →
              read-cede-file s filename >>= λ where
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
    else ((ensure-ast-depsh filename s >>= aux-up-to-date filename) >>= cont (stringset-insert seen filename))
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
  log-files-to-check s = logRope s ([[ "\n" ]] ⊹⊹ (h (trie-mappings (toplevel-state.is s)))) where
    h : 𝕃 (string × include-elt) → rope
    h [] = [[]]
    h ((fn , ie) :: t) = [[ "file: " ]] ⊹⊹ [[ fn ]] ⊹⊹ [[ "\nadd-symbols: " ]] ⊹⊹ [[ 𝔹-to-string (include-elt.need-to-add-symbols-to-context ie) ]] ⊹⊹ [[ "\ndo-type-check: " ]] ⊹⊹ [[ 𝔹-to-string (include-elt.do-type-check ie) ]] ⊹⊹ [[ "\n\n" ]] ⊹⊹ h t

  {- this function checks the given file (if necessary), updates .cede and .rkt files (again, if necessary), and replies on stdout if appropriate -}
  checkFile : (string → IO ⊤) → toplevel-state → filepath → (should-print-spans : 𝔹) → IO toplevel-state
  checkFile progressUpdate s filename should-print-spans = 
    update-asts s filename >>= λ s →
    log-files-to-check s >>
    logMsg s (𝕃-to-string (λ {(im , fn) → "im: " ^ im ^ ", fn: " ^ fn})
                "; "
                (trie-mappings (include-elt.import-to-dep (get-include-elt s filename)))) >>
    process-file progressUpdate (logMsg s) s filename (fileBaseName filename) >>= finish
    where
          reply : toplevel-state → IO ⊤
          reply s with get-include-elt-if s filename
          reply s | nothing = putStrLn (global-error-string ("Internal error looking up information for file " ^ filename ^ "."))
          reply s | just ie =
             if should-print-spans then
               putJson (include-elt-spans-to-json ie)
             else return triv
          finish : (toplevel-state × file × string × string × params × qualif) → IO toplevel-state
          finish (s @ (mk-toplevel-state ip mod is Γ logFilePath) , f , ret-mod) =
            logMsg s ("Started reply for file " ^ filename) >> -- Lazy, so checking has not been calculated yet?
            reply s >>
            logMsg s ("Finished reply for file " ^ filename) >>
            logMsg s ("Files with updated spans:\n" ^ 𝕃-to-string (λ x → x) "\n" mod) >>
            let Γ = ctxt-set-current-mod Γ ret-mod in
              writeo mod >>r -- Should process-file now always add files to the list of modified ones because now the cede-/rkt-up-to-date fields take care of whether to rewrite them?
              mk-toplevel-state ip [] is Γ logFilePath -- Reset files with updated spans
              where
                writeo : 𝕃 string → IO ⊤
                writeo [] = return triv
                writeo (f :: us) =
                  writeo us >>
                  --let ie = get-include-elt s f in
                  write-aux-files s f
                  --  (if cedille-options.options.make-rkt-files options && ~ include-elt.rkt-up-to-date ie then (write-rkt-file f (toplevel-state.Γ s) ie rkt-filename) else return triv)

  -- this is the function that handles requests (from the frontend) on standard input
  {-# TERMINATING #-}
  readCommandsFromFrontend : toplevel-state → IO ⊤
  readCommandsFromFrontend s =
      getLine >>= λ input →
      logMsg s ("Frontend input: " ^ input) >>
      let input-list : 𝕃 string 
          input-list = string-split (undo-escape-string input) delimiter in
      handleCommands input-list s >>= readCommandsFromFrontend
    where
    errorCommand : 𝕃 string → toplevel-state → IO ⊤
    errorCommand ls s = putStrLn (global-error-string "Invalid command sequence \\\\\"" ^ (𝕃-to-string (λ x → x) ", " ls) ^ "\\\\\".")

    debugCommand : toplevel-state → IO ⊤
    debugCommand s = putStrLn (escape-string (toplevel-state-to-string s))

    checkCommand : 𝕃 string → toplevel-state → IO toplevel-state
    checkCommand (input :: []) s =
      canonicalizePath input >>= λ input-filename →
      checkFile progressUpdate (set-include-path s (cedille-options.include-path-insert (takeDirectory input-filename) (toplevel-state.include-path s))) input-filename tt {- should-print-spans -}
    checkCommand ls s = errorCommand ls s >>r s

    createArchive-h : toplevel-state → trie json → 𝕃 string → json
    createArchive-h s t (filename :: filenames) with trie-contains t filename | get-include-elt-if s filename
    ...| ff | just ie = createArchive-h s (trie-insert t filename $ include-elt-to-archive ie) (filenames ++ include-elt.deps ie)
    ...| _ | _ = createArchive-h s t filenames
    createArchive-h s t [] = json-object $ trie-mappings t

    createArchive : toplevel-state → string → json
    createArchive s filename = createArchive-h s empty-trie (filename :: [])

    archiveCommand : 𝕃 string → toplevel-state → IO toplevel-state
    archiveCommand (input :: []) s =
      canonicalizePath input >>= λ filename →
      update-asts s filename >>= λ s →
      process-file (λ _ → return triv) (λ _ → return triv) s
        filename (fileBaseName filename) >>=c λ s _ →
      putRopeLn (json-to-rope (createArchive s filename)) >>r s
    archiveCommand ls s = errorCommand ls s >>r s

    handleCommands : 𝕃 string → toplevel-state → IO toplevel-state
    handleCommands ("progress stub" :: xs) = return
    handleCommands ("status ping" :: xs) s = putStrLn "idle" >> return s
    handleCommands ("check" :: xs) s = checkCommand xs s
    handleCommands ("debug" :: []) s = debugCommand s >>r s
    handleCommands ("elaborate" :: fm :: to :: []) s = elab-all s fm to >>r s
    handleCommands ("interactive" :: xs) s = interactive-cmd xs s >>r s
    handleCommands ("archive" :: xs) s = archiveCommand xs s
    handleCommands ("br" :: xs) s = putJson interactive-not-br-cmd-msg >>r s
  --            handleCommands ("find" :: xs) s = findCommand xs s
    handleCommands xs s = errorCommand xs s >>r s

{-
  mk-new-toplevel-state : IO toplevel-state
  mk-new-toplevel-state =
    let s = new-toplevel-state (cedille-options.options.include-path options) in
    maybe-else' (cedille-options.options.datatype-encoding options) (return s)
      λ fp → readFiniteFile fp >>= λ de → case parseStart de of λ where
        (Left (Left e)) → putStrLn ("Lexical error in datatype encoding at position " ^ e) >>r s
        (Left (Right e)) → putStrLn ("Parse error in datatype encoding at position " ^ e) >>r s
        (Right de) → {!!}
-}

  processFile : (logFilePath : filepath) → string → IO toplevel-state
  processFile logFilePath input-filename =
    checkFile progressUpdate (new-toplevel-state logFilePath (cedille-options.include-path-insert (takeDirectory input-filename)
    (cedille-options.options.include-path options))) input-filename ff

  typecheckFile : (logFilePath : filepath) → string → IO toplevel-state
  typecheckFile logFilePath f =
    processFile logFilePath f >>= λ s →
    let ie = get-include-elt s f in
      if include-elt.err ie
      then die (string-to-𝕃char ("Type Checking Failed"))
      else return s

  -- function to process command-line arguments
  processArgs : (logFilePath : filepath) → cedille-args → IO ⊤
  -- this is the case for when we are called with a single command-line argument, the name of the file to process
  processArgs logFilePath (mk-cedille-args _ minput-filename about help do-elab confirm-read-stdin) =
    if help then
      showCedilleUsage
    else if about then
      say-about options-filepath
    else
      maybe-else' minput-filename
       (ifM confirm-read-stdin 
         $ readCommandsFromFrontend (new-toplevel-state logFilePath (cedille-options.options.include-path options)))
      (λ input-filename →
        canonicalizePath input-filename >>= λ input-filename' →
        typecheckFile logFilePath input-filename' >>= λ s →
        whenM do-elab (λ target-dir → elab-all s input-filename' target-dir))

  main' : cedille-args → IO ⊤
  main' args =
    maybeClearLogFile >>= λ logFilePath → 
    logMsg' logFilePath ("Started Cedille process (compiled at: " ^ utcToString compileTime ^ ")") >>
    processArgs logFilePath args

getCedilleArgs : IO cedille-args
getCedilleArgs = getArgs >>= λ where
                                     -- only read from stdin if there are no args at all
                                [] → return $ record default-cedille-args {confirm-read-stdin = tt}
                                args → getCedilleArgsH args default-cedille-args
  where
  bad-opts-flag : IO ⊤
  bad-opts-flag  = putStrLn "warning: flag --options should be followed by a Cedille options file"

  unknown-flag : string → IO ⊤
  unknown-flag f = putStrLn $ "warning: unknown flag " ^ f

  -- allow for later --options to override earlier. This is a bash idiom
  getCedilleArgsH : 𝕃 string → cedille-args → IO cedille-args
  getCedilleArgsH ("--options" :: y :: xs) args =
    getCedilleArgsH xs (record args { opts-file = just y})
  getCedilleArgsH ("--options" :: []) args =   
    bad-opts-flag >> return args
  getCedilleArgsH ("--about" :: xs) args =
    getCedilleArgsH xs (record args { about = tt })
  getCedilleArgsH ("--help" :: xs) args = 
    getCedilleArgsH xs (record args { help = tt })
  getCedilleArgsH ("--elab" :: to :: xs) args =
    getCedilleArgsH xs (record args { do-elab = just to})
  getCedilleArgsH (x :: []) args =
    -- assume it is a .ced file to check
    return $ record args {file-to-process = just x}
  getCedilleArgsH (x :: y :: xs) args =
    unknown-flag x >> return args
  getCedilleArgsH [] args = return args 

process-encoding : filepath → cedille-options.options → IO cedille-options.options
process-encoding ofp ops @ (cedille-options.mk-options ip _ _ _ _ _ de _ _ _ _) =
  maybe-else' de (return ops) λ de-f →
  let de = fst de-f
      s = new-toplevel-state "no logfile path" (cedille-options.include-path-insert (takeDirectory de) ip) in
  update-asts s de >>= λ s →
  process-encoding-file s de >>= λ f? →
  maybe-else' f? (return ops) λ ast~ →
  return (record ops {datatype-encoding = just (de , just ast~)})
  where
  ops' = record ops {datatype-encoding = nothing; use-cede-files = ff}
  open main-with-options compileTime ofp ops' die
  open import spans ops' {IO}
  open import toplevel-state ops' {IO}
  open import process-cmd ops' {IO} (λ _ → return triv) (λ _ → return triv)
  open import syntax-util
  open import ctxt

  process-encoding-file : toplevel-state → filepath → IO (maybe file)
  process-encoding-file s fp with get-include-elt-if s fp >>= include-elt.ast
  ...| nothing = putStrLn ("Error looking up datatype encoding information from file " ^ fp) >> return nothing
  ...| just (ExModule is pi1 pi2 mn ps cs pi3) =
    (process-cmds (record s {Γ = ctxt-initiate-file (toplevel-state.Γ s) fp mn}) (map ExCmdImport is) >>=c λ s is' →
     process-params s first-position [] >>=c λ s _ →
     check-and-add-params (toplevel-state.Γ s) (params-end-pos first-position ps) ps >>=c λ Γₚₛ ps~ →
     process-cmds (record s {Γ = Γₚₛ}) cs >>=c λ s cs →
     return2 ps~ (is' ++ cs)) empty-spans >>=c uncurry λ ps cs _ →
    return (just (Module mn ps cs))


-- main entrypoint for the backend
main : IO ⊤
main = initializeStdoutToUTF8 >>
       initializeStdinToUTF8 >>
       setStdoutNewlineMode >>
       setStdinNewlineMode >>
       setToLineBuffering >>
       getCedilleArgs >>= λ args →
       maybe-else' (cedille-args.opts-file args)
         (findOptionsFile >>= readOptions) (readOptions ∘ just) >>=c λ ofp ops →
       let log = cedille-options.options.generate-logs ops in
       process-encoding ofp (record ops {generate-logs = ff}) >>= λ ops →
       let args = record args { opts-file = just ofp } in 
       let ops = record ops { generate-logs = log ;
                              show-progress-updates = ~ (cedille-args.confirm-read-stdin args) } in
       main-with-options.main' compileTime ofp ops die args
