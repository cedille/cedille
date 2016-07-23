module main where

import parse
import run
open import lib
open import cedille-types

-- for parser for Cedille source files
import cedille
module parsem = parse cedille.gratr2-nt ptr
open parsem.pnoderiv cedille.rrs cedille.cedille-rtn
module pr = run ptr
open pr.noderiv {- from run.agda -}

-- for parser for options files
import options
import options-types
module parsem2 = parse options.gratr2-nt options-types.ptr
module options-parse = parsem2.pnoderiv options.rrs options.options-rtn
module pr2 = run options-types.ptr
module options-run = pr2.noderiv

open import classify
open import ctxt
open import constants
open import conversion
open import general-util
open import process-cmd 
open import rec
open import spans
open import syntax-util
open import to-string
open import toplevel-state

opts : Set
opts = options-types.opts

dot-cedille-directory : string → string 
dot-cedille-directory dir = combineFileNames dir ".cedille"

cede-filename : (ced-path : string) → string
cede-filename ced-path = 
  let dir = takeDirectory ced-path in
  let unit-name = base-filename (takeFileName ced-path) in
    combineFileNames (dot-cedille-directory dir) (unit-name ^ ".cede")

-- .cede files are just a dump of the spans, prefixed by 'e' if there is an error
write-cede-file : (ced-path : string) → (err : 𝔹) → string → IO ⊤
write-cede-file ced-path err contents = 
--  putStr ("write-cede-file " ^ ced-path ^ " : " ^ contents ^ "\n") >>
  let dir = takeDirectory ced-path in
    createDirectoryIfMissing ff (dot-cedille-directory dir) >>
    writeFile (cede-filename ced-path) ((if err then "e" else "") ^ contents) 

-- we assume the cede file is known to exist at this point
read-cede-file : (ced-path : string) → IO (𝔹 × string)
read-cede-file ced-path = 
  get-file-contents (cede-filename ced-path) >>= λ c → finish c
  where finish : maybe string → IO (𝔹 × string)
        finish nothing = return (tt , global-error-string ("Could not read the file " ^ cede-filename ced-path ^ "."))
        finish (just ss) with string-to-𝕃char ss
        finish (just ss)  | ('e' :: ss') = forceFileRead ss >> return (tt , 𝕃char-to-string ss')
        finish (just ss) | _ = forceFileRead ss >> return (ff , ss)
  
add-cedille-extension : string → string
add-cedille-extension x = x ^ "." ^ cedille-extension 

cedille-get-path : (dirs : 𝕃 string) → (unit-name : string) → IO string
cedille-get-path [] unit-name = return (add-cedille-extension unit-name) -- assume the current directory if the unit is not found 
cedille-get-path (dir :: dirs) unit-name =
  let e = combineFileNames dir (add-cedille-extension unit-name) in
    doesFileExist e >>= λ b → 
    if b then
      return e
    else
      cedille-get-path dirs unit-name

ced-file-up-to-date : (ced-path : string) → IO 𝔹
ced-file-up-to-date ced-path =
  let e = cede-filename ced-path in
    doesFileExist e >>= λ b → 
    if b then
      fileIsOlder ced-path e
    else
      return ff

paths-to-𝕃string : options-types.paths → 𝕃 string
paths-to-𝕃string options-types.PathsNil = []
paths-to-𝕃string (options-types.PathsCons p ps) = p :: paths-to-𝕃string ps

opts-get-include-path : opts → 𝕃 string
opts-get-include-path options-types.OptsNil = []
opts-get-include-path (options-types.OptsCons (options-types.Lib ps) oo) = (paths-to-𝕃string ps) ++ opts-get-include-path oo
--opts-get-include-path (options-types.OptsCons _ oo) = opts-get-include-path oo


{- reparse the given file, and update its include-elt in the toplevel-state appropriately -}
reparse : toplevel-state → (unit-name : string) → (filename : string) → IO toplevel-state
reparse s unit-name filename = 
--   putStr ("reparsing " ^ unit-name ^ " " ^ filename ^ "\n") >>
   doesFileExist filename >>= λ b → 
     (if b then
         (readFiniteFile filename >>= (λ f → return (processText f)))
      else return (error-include-elt ("The file " ^ filename ^ " could not be opened for reading."))) >>= λ ie →
        return (set-include-elt s unit-name ie)
  where processText : string → include-elt
        processText x with string-to-𝕃char x
        processText x | s with runRtn s
        processText x | s | inj₁ cs =
           error-include-elt ("Parse error in file " ^ filename ^ " at position " ^ (ℕ-to-string (length s ∸ length cs)) ^ ".")
        processText x | s | inj₂ r with rewriteRun r
        processText x | s | inj₂ r | ParseTree (parsed-start t) :: [] = 
          new-include-elt filename t
        processText x | s | inj₂ r | _ = error-include-elt ("Parse error in file " ^ filename ^ ".")

add-spans-if-up-to-date : (up-to-date : 𝔹) → (filename : string) → include-elt → IO include-elt
add-spans-if-up-to-date up-to-date filename ie = 
  if up-to-date then
    (read-cede-file filename >>= finish)
  else
    return ie
  where finish : 𝔹 × string → IO include-elt
        finish (err , ss) = return (set-do-type-check-include-elt (set-spans-string-include-elt ie err ss) ff)

{- make sure that the current ast and dependencies are stored in the
   toplevel-state, updating the state as needed. -}
ensure-ast-deps : toplevel-state → (unit-name : string) → (filename : string) → IO toplevel-state
ensure-ast-deps s unit-name filename with get-include-elt-if s unit-name
ensure-ast-deps s unit-name filename | nothing = 
  reparse s unit-name filename >>= λ s → 
  ced-file-up-to-date filename >>= λ up-to-date → 
  add-spans-if-up-to-date up-to-date filename (get-include-elt s unit-name) >>= λ ie →
  return (set-include-elt s unit-name ie)
ensure-ast-deps s unit-name filename | just ie =
  ced-file-up-to-date filename >>= λ up-to-date → 
    if up-to-date then 
      (add-spans-if-up-to-date up-to-date filename (get-include-elt s unit-name) >>= λ ie →
       return (set-include-elt s unit-name ie))
    else reparse s unit-name filename
     
{-# NO_TERMINATION_CHECK #-}
update-astsh : stringset {- seen already -} → toplevel-state → (unit-name : string) → 
               IO (stringset {- seen already -} × toplevel-state)
update-astsh seen s unit-name = 
  cedille-get-path (toplevel-state.include-path s) unit-name >>= λ input-filename → 
--  putStr ("update-astsh [input-filename = " ^ input-filename ^ "]\n") >>
  if stringset-contains seen input-filename then return (seen , s)
  else (ensure-ast-deps s unit-name input-filename >>= cont (stringset-insert seen input-filename))
  where cont : stringset → toplevel-state → IO (stringset × toplevel-state)
        cont seen s with get-include-elt s unit-name
        cont seen s | ie with include-elt.deps ie 
        cont seen s | ie | ds = 
          proc seen s ds 
          where proc : stringset → toplevel-state → 𝕃 string → IO (stringset × toplevel-state)
                proc seen s [] = 
                  if (list-any (get-do-type-check s) ds) 
                  then return (seen , set-include-elt s unit-name (set-do-type-check-include-elt ie tt)) 
                  else return (seen , s)
                proc seen s (d :: ds) = update-astsh seen s d >>= λ p → 
                                        proc (fst p) (snd p) ds

update-asts : toplevel-state → (unit-name : string) → IO toplevel-state
update-asts s unit-name = update-astsh empty-stringset s unit-name >>= λ p → 
  return (snd p)

checkFile : toplevel-state → (unit-name : string) → (should-print-spans : 𝔹) → IO toplevel-state
checkFile s unit-name should-print-spans = 
--  putStr ("checkFile " ^ unit-name ^ "\n") >>
  update-asts s unit-name >>= λ s → 
  finish (process-unit s unit-name)
 
  where reply : toplevel-state → IO ⊤
        reply s with get-include-elt-if s unit-name
        reply s | nothing = 
           putStr (global-error-string 
                     ("Internal error looking up information for unit " ^ unit-name ^ "."))
        reply s | just ie =
           if should-print-spans then putStr (include-elt.ss ie) 
           else return triv
        finish : toplevel-state → IO toplevel-state
        finish s with s
        finish s | mk-toplevel-state ip mod is Γ = 
          writeo mod >>
          reply s >>
          return (mk-toplevel-state ip [] is Γ)
          where writeo : 𝕃 string → IO ⊤
                writeo [] = return triv
                writeo (unit :: us) =
                 let ie = get-include-elt s unit in
--                   putStr ("writeo " ^ unit ^ " with path " ^ (include-elt.path ie) ^ ".\n") >>
                   write-cede-file (include-elt.path ie) (include-elt.err ie) (include-elt.ss ie) >>
                   writeo us

{-# NO_TERMINATION_CHECK #-}
readFilenamesForProcessing : toplevel-state → IO ⊤
readFilenamesForProcessing s =
  getLine >>= (λ input-filename → 
     checkFile (set-include-path s (toplevel-state.include-path s))
       (base-filename (takeFileName input-filename)) tt {- should-print-spans -} >>= λ s → 
     readFilenamesForProcessing s)

processArgs : opts → 𝕃 string → IO ⊤ 
processArgs oo (input-filename :: []) with (base-filename (takeFileName input-filename)) 
processArgs oo (input-filename :: []) | unit-name = 
  checkFile (new-toplevel-state (opts-get-include-path oo)) unit-name ff {- should-print-spans -} >>= finish
  where finish : toplevel-state → IO ⊤
        finish s = 
          let ie = get-include-elt s unit-name in
          if include-elt.err ie then putStr (include-elt.ss ie) else return triv
processArgs oo [] = readFilenamesForProcessing (new-toplevel-state (opts-get-include-path oo))
processArgs oo xs = putStr ("Run with the name of one file to process, or run with no command-line arguments and enter the\n"
                         ^ "names of files one at a time followed by newlines (this is for the emacs mode).\n")

processOptions : string → string → (string ⊎ options-types.opts)
processOptions filename s with string-to-𝕃char s
processOptions filename s | i with options-parse.runRtn i
processOptions filename s | i | inj₁ cs =
  inj₁ ("Parse error in file " ^ filename ^ " at position " ^ (ℕ-to-string (length i ∸ length cs)) ^ ".")
processOptions filename s | i | inj₂ r with options-parse.rewriteRun r
processOptions filename s | i | inj₂ r | options-run.ParseTree (options-types.parsed-start (options-types.File oo)) :: [] = inj₂ oo
processOptions filename s | i | inj₂ r | _ =  inj₁ ("Parse error in file " ^ filename ^ ". ")

readOptions : IO (string ⊎ options-types.opts)
readOptions =
  getHomeDirectory >>= λ homedir →
    let homecedir = dot-cedille-directory homedir in
    let optsfile = combineFileNames homecedir options-file-name in
      createDirectoryIfMissing ff homecedir >>
      doesFileExist optsfile >>= λ b → 
       if b then
         (readFiniteFile optsfile >>= λ f → return (processOptions optsfile f))
       else
         (return (inj₂ options-types.OptsNil))

main : IO ⊤
main = readOptions >>= next
  where next : string ⊎ options-types.opts → IO ⊤
        next (inj₁ s) = putStr (global-error-string s)
        next (inj₂ oo) = getArgs >>= processArgs oo

