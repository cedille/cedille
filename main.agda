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

open import ctxt
open import constants

-- keep track of our includes
data include-state-t : Set where
  include-state : stringset → include-state-t

new-include-state : include-state-t
new-include-state = include-state empty-stringset

data cedille-state-t : Set where
  cedille-state : include-state-t → ctxt-t → cedille-state-t

new-cedille-state : cedille-state-t
new-cedille-state = cedille-state new-include-state new-ctxt

-- these are mutually recursive due to Import commands
{-# NO_TERMINATION_CHECK #-}
process-cmd : cmd → cedille-state-t → IO cedille-state-t
process-cmds : cmds → cedille-state-t → IO cedille-state-t
process-start : start → cedille-state-t → IO cedille-state-t
processFile : string → cedille-state-t → IO cedille-state-t

process-cmd (ClassKind x) s = return s
process-cmd (DefCmd x) s = return s
process-cmd (Echeck x) s = return s
process-cmd (Import x) (cedille-state (include-state is) Γ) = 
  let s = (cedille-state (include-state is) Γ) in
  let filename = (x ^ "." ^ cedille-extension) in
    if stringset-contains is filename then return s
    else processFile filename s
process-cmd (Normalize x) s = return s
process-cmd (Rec x x₁ x₂ x₃ x₄ x₅) s = return s

process-cmds (CmdsNext c cs) s = process-cmd c s >>= process-cmds cs
process-cmds (CmdsStart c) s = process-cmd c s

process-start (Cmds cs) s = process-cmds cs s

-- process the given input file, after adding it to the include state
processFile input-filename s with s 
processFile input-filename s | (cedille-state (include-state is) Γ) = 
    (readFiniteFile input-filename) >>= processText
    where processText : string → IO cedille-state-t
          processText x with runRtn (string-to-𝕃char x)
          processText x | inj₁ cs = 
            putStr ("In file \"" ^ input-filename ^ "\":") >>
            putStr "Characters left before failure : " >> putStr (𝕃char-to-string cs) >> putStr "\nCannot proceed to parsing.\n" 
            >> return s
          processText x | inj₂ r with rewriteRun r
          processText x | inj₂ r | (ParseTree (parsed-start p) :: []) = 
            process-start p (cedille-state (include-state (stringset-insert is input-filename)) Γ)
          processText x | inj₂ r | _ = putStr ("Parse error in file \"" ^ x ^ "\"\n") >> return s

processArgs : 𝕃 string → IO ⊤ 
processArgs (input-filename :: []) = 
  processFile input-filename new-cedille-state >>= finish
  where finish : cedille-state-t → IO ⊤
        finish (cedille-state (include-state is) Γ) = putStr (string-concat-sep "\n" (stringset-strings is)) >> putStr "\n"
processArgs (x :: xs) = putStr ("Unknown option " ^ x ^ "\n")
processArgs [] = putStr "Please run with the name of a file to process.\n"

main : IO ⊤
main = getArgs >>= processArgs 

