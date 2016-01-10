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

open import classify
open import ctxt
open import constants
open import rec
open import spans
open import syntax-util
open import to-string

-- keep track of our includes
data include-state : Set where
  mk-include-state : stringset → include-state

new-include-state : include-state
new-include-state = mk-include-state empty-stringset

data toplevel-state : Set where
  mk-toplevel-state : include-state → ctxt → spans → toplevel-state

new-toplevel-state : toplevel-state
new-toplevel-state = mk-toplevel-state new-include-state new-ctxt empty-spans

{- these are mutually recursive due to Import commands.
   dir is the directory to search for includes (we should 
   add a more sophisticated mechanism later) -}

{-# NO_TERMINATION_CHECK #-}
process-cmd : (dir : string) → cmd → toplevel-state → IO toplevel-state
process-cmds : (dir : string) → cmds → toplevel-state → IO toplevel-state
process-start : (dir : string) → start → toplevel-state → IO toplevel-state
processFile : (dir : string) → (file : string) → toplevel-state → IO toplevel-state

process-cmd dir (DefTerm pi x (Type tp) t pi') (mk-toplevel-state (mk-include-state is) Γ ss) = 
  let ss' = (check-type Γ tp (just star) ≫span 
             check-term Γ t (just tp) ≫span 
             spanM-add (DefTerm-span pi x tt (just tp) t pi')) ss in
    return (mk-toplevel-state (mk-include-state is) (ctxt-term-def x t tp Γ) (snd ss'))
process-cmd dir (DefTerm pi x NoCheckType t pi') (mk-toplevel-state (mk-include-state is) Γ ss) = 
  let ss' = (check-term Γ t nothing ≫=span λ mtp → spanM-add (DefTerm-span pi x ff mtp t pi') ≫span spanMr mtp) ss in
    return (mk-toplevel-state (mk-include-state is) (h (fst ss')) (snd ss'))
  where h : maybe type → ctxt
        h nothing = ctxt-term-udef x t Γ
        h (just tp) = ctxt-term-def x t tp Γ
process-cmd dir (CheckTerm t m pi) (mk-toplevel-state (mk-include-state is) Γ ss) = 
  return (mk-toplevel-state (mk-include-state is) Γ ss)
process-cmd dir (DefType pi x k tp pi') (mk-toplevel-state (mk-include-state is) Γ ss) = 
  return (mk-toplevel-state (mk-include-state is) Γ ss)
process-cmd dir (CheckType tp m pi) (mk-toplevel-state (mk-include-state is) Γ ss) = 
  return (mk-toplevel-state (mk-include-state is) Γ ss)
process-cmd dir (DefKind pi x _ k pi') (mk-toplevel-state (mk-include-state is) Γ ss) = 
  return (mk-toplevel-state (mk-include-state is) Γ ss)
process-cmd dir (CheckKind k _ pi) (mk-toplevel-state (mk-include-state is) Γ ss) = 
  return (mk-toplevel-state (mk-include-state is) Γ ss)
process-cmd dir (Import x) s with s
process-cmd dir (Import x) s | mk-toplevel-state (mk-include-state is) _ _ = 
  let file = x ^ "." ^ cedille-extension in
    if stringset-contains is (combineFileNames dir file) then return s
    else processFile dir file s
process-cmd dir (Normalize x) s = return s
process-cmd dir (Rec pi name params inds ctors body us pi') (mk-toplevel-state i Γ ss) = 
    let p = process-rec-cmd Γ pi name params inds ctors body us pi' ss in
    return (mk-toplevel-state i (fst p) (snd p))

process-cmds dir (CmdsNext c cs) s = process-cmd dir c s >>= cont
  where cont : toplevel-state → IO toplevel-state
        cont s with s 
        cont s | (mk-toplevel-state i c ss) = 
          if global-error-p ss then return s else process-cmds dir cs s
process-cmds dir (CmdsStart c) s = process-cmd dir c s

process-start dir (Cmds cs) s = process-cmds dir cs s

-- process the given input file, after adding it to the include state
processFile dir file s with s | combineFileNames dir file
processFile dir file s | (mk-toplevel-state (mk-include-state is) Γ ss) | input-filename = 
  doesFileExist input-filename >>= λ b → 
  if b then
    (readFiniteFile input-filename) >>= processText
  else
    return (mk-toplevel-state (mk-include-state is) Γ
             (global-error ("Cannot open file " ^ input-filename ^ " for reading") nothing))
  where processText : string → IO toplevel-state
        processText x with runRtn (string-to-𝕃char x)
        processText x | inj₁ cs = 
          return (mk-toplevel-state (mk-include-state is) Γ
                   (global-error ("Parse error in file " ^ input-filename ^ ". "
                                 ^ "Characters left before failure : " ^ (𝕃char-to-string cs)) nothing))
        processText x | inj₂ r with rewriteRun r
        processText x | inj₂ r | (ParseTree (parsed-start p) :: []) = 
          process-start dir p (mk-toplevel-state (mk-include-state (stringset-insert is input-filename)) Γ ss)
            >>= finish
          where finish : toplevel-state → IO toplevel-state
                finish (mk-toplevel-state i Γ ss') = 
                 let base = base-filename file in
                   writeFile (combineFileNames dir (base ^ ".cede")) (spans-to-string ss') >>
                      -- do not return the newly added spans, unless we have a global error
                   return (mk-toplevel-state i Γ (if global-error-p ss' then ss' else ss))

        processText x | inj₂ r | _ = return (mk-toplevel-state (mk-include-state is) Γ
                                              (global-error ("Parse error in file " ^ input-filename ^ ".") nothing))

processArgs : 𝕃 string → IO ⊤ 
processArgs (input-filename :: []) = 
  processFile (takeDirectory input-filename) (takeFileName input-filename) new-toplevel-state >>= finish
  where finish : toplevel-state → IO ⊤
        finish (mk-toplevel-state (mk-include-state is) Γ ss) = 
          if global-error-p ss then putStr (spans-to-string ss) else return triv
processArgs (x :: xs) = putStr ("Unknown option " ^ x ^ "\n")
processArgs [] = putStr "Please run with the name of a file to process.\n"

--writing the include state: putStr (string-concat-sep "\n" (stringset-strings is))

main : IO ⊤
main = getArgs >>= processArgs 

