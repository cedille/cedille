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

open import tpstate
open import check

process-cmd : cmd → tpstate → error-t tpstate
process-cmd (DefCmd d) s = check-def s d
process-cmd (Echeck (Tp trm tp) e) s = check-term s empty-ctxt e trm tp ≫=err λ m → no-error (add-msg m s)
process-cmd (Echeck (Knd tp knd) e) s = check-type s empty-ctxt e tp knd ≫=err λ m → no-error (add-msg m s)
process-cmd (Kcheck k e) s = check-kind s empty-ctxt e k ≫=err λ m → no-error (add-msg m s)

process-cmds : cmds → tpstate → error-t tpstate
process-cmds (CmdsStart c) s = process-cmd c s
process-cmds (CmdsNext c cs) s = process-cmd c s ≫=err process-cmds cs

process-start : start → string
process-start (Cmds cs) with process-cmds cs (mk-tpstate "" empty-trie empty-trie empty-trie empty-trie)
process-start (Cmds cs) | yes-error s = s ^ "\n"
process-start (Cmds cs) | no-error (mk-tpstate s _ _ _ _) = s ^ "\n"

process : Run → string
process (ParseTree (parsed-start p) :: []) = process-start p
process r = "Parsing failure (run with -" ^ "-showParsed).\n"

putStrRunIf : 𝔹 → Run → IO ⊤
putStrRunIf tt r = putStr (Run-to-string r) >> putStr "\n"
putStrRunIf ff r = return triv

processArgs : (showParsed : 𝔹) → 𝕃 string → IO ⊤ 
processArgs showParsed (input-filename :: []) = (readFiniteFile input-filename) >>= processText
  where processText : string → IO ⊤
        processText x with runRtn (string-to-𝕃char x)
        processText x | s with s
        processText x | s | inj₁ cs = putStr "Characters left before failure : " >> putStr (𝕃char-to-string cs) >> putStr "\nCannot proceed to parsing.\n"
        processText x | s | inj₂ r with rewriteRun r
        processText x | s | inj₂ r | r' with putStrRunIf showParsed r'
        processText x | s | inj₂ r | r' | sr' = sr' >> putStr (process r')
                                     
processArgs showParsed ("--showParsed" :: xs) = processArgs tt xs 
processArgs showParsed (x :: xs) = putStr ("Unknown option " ^ x ^ "\n")
processArgs showParsed [] = putStr "Please run with the name of a file to process.\n"

main : IO ⊤
main = getArgs >>= processArgs ff 

