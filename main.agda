module main where

import parse
open import lib
open import cedille-types
import cedille

module parsem = parse cedille.gratr2-nt ptr
open parsem
open parsem.pnoderiv cedille.rrs cedille.cedille-rtn
open import run ptr
open noderiv {- from run.agda -}

open import cedille-state hiding (mk-cedille-state)
open import classify
open import ctxt
open import constants
open import spans
open import to-string

-- keep track of our includes
data include-state : Set where
  mk-include-state : stringset → include-state

new-include-state : include-state
new-include-state = mk-include-state empty-stringset

data toplevel-state : Set where
  mk-toplevel-state : include-state → cedille-state → toplevel-state

new-toplevel-state : toplevel-state
new-toplevel-state = mk-toplevel-state new-include-state new-cedille-state

{- these are mutually recursive due to Import commands.
   dir is the directory to search for includes (we should 
   add a more sophisticated mechanism later) -}

{-# NO_TERMINATION_CHECK #-}
process-cmd : (dir : string) → cmd → toplevel-state → IO toplevel-state
process-cmds : (dir : string) → cmds → toplevel-state → IO toplevel-state
process-start : (dir : string) → start → toplevel-state → IO toplevel-state
processFile : (dir : string) → (file : string) → toplevel-state → IO toplevel-state

process-cmd dir (ClassKind x) s = return s
process-cmd dir (DefCmd x) s = return s
process-cmd dir (Echeck x) s = return s
process-cmd dir (Import x) (mk-toplevel-state (mk-include-state is) c) = 
  let s = (mk-toplevel-state (mk-include-state is) c) in
  let file = x ^ "." ^ cedille-extension in
    if stringset-contains is (combineFileNames dir file) then return s
    else processFile dir file s
process-cmd dir (Normalize x) s = return s
process-cmd dir (Rec pi name params inds ctors body us pi') (mk-toplevel-state i c) = 
  let m = rec-compute-kind params inds ≫=ced λ k → 
           (cedM-add-span (mk-span Rec-name pi pi' (Rec-explain name :: kind-data k :: [])))
  in
    return (mk-toplevel-state i (snd (m c)))

process-cmds dir (CmdsNext c cs) s = process-cmd dir c s >>= cont
  where cont : toplevel-state → IO toplevel-state
        cont s with s 
        cont s | (mk-toplevel-state i c) = 
          if ced-global-error-p c then return s else process-cmds dir cs s
process-cmds dir (CmdsStart c) s = process-cmd dir c s

process-start dir (Cmds cs) s = process-cmds dir cs s

-- process the given input file, after adding it to the include state
processFile dir file s with s | combineFileNames dir file
processFile dir file s | (mk-toplevel-state (mk-include-state is) c) | input-filename = 
  doesFileExist input-filename >>= λ b → 
  if b then
    (readFiniteFile input-filename) >>= processText
  else
    return (mk-toplevel-state (mk-include-state is)
             (ced-global-error ("Cannot open file " ^ input-filename ^ " for reading") nothing))
  where processText : string → IO toplevel-state
        processText x with runRtn (string-to-𝕃char x)
        processText x | inj₁ cs = 
          putStr ("In file \"" ^ input-filename ^ "\":") >>
          putStr "Characters left before failure : " >> putStr (𝕃char-to-string cs) >> putStr "\nCannot proceed to parsing.\n" 
          >> return s
        processText x | inj₂ r with rewriteRun r
        processText x | inj₂ r | (ParseTree (parsed-start p) :: []) = 
          process-start dir p (mk-toplevel-state (mk-include-state (stringset-insert is input-filename)) c)
            >>= finish
          where finish : toplevel-state → IO toplevel-state
                finish (mk-toplevel-state i c') = 
                 let base = base-filename file in
                   writeFile (combineFileNames dir (base ^ ".cede")) (ced-spans-to-string c') >>
                      -- do not return the newly added spans, unless we have a global error
                   return (mk-toplevel-state i (if ced-global-error-p c' then c' else c))

        processText x | inj₂ r | _ = putStr ("Parse error in file \"" ^ x ^ "\"\n") >> return s

processArgs : 𝕃 string → IO ⊤ 
processArgs (input-filename :: []) = 
  processFile (takeDirectory input-filename) (takeFileName input-filename) new-toplevel-state >>= finish
  where finish : toplevel-state → IO ⊤
        finish (mk-toplevel-state (mk-include-state is) c) = 
          if ced-global-error-p c then putStr (ced-spans-to-string c) else return triv
processArgs (x :: xs) = putStr ("Unknown option " ^ x ^ "\n")
processArgs [] = putStr "Please run with the name of a file to process.\n"

--writing the include state: putStr (string-concat-sep "\n" (stringset-strings is))

main : IO ⊤
main = getArgs >>= processArgs 

