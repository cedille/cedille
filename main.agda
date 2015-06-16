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

process-def : def → tpstate → error-t tpstate
process-def (Tdefine v t) (mk-tpstate o d td yd kd) = no-error (mk-tpstate o (trie-insert d v t) td yd kd)
process-def (Edefine v (Tp trm tp) e) s = 
  check-term s empty-evctxt e trm tp ≫=err λ m → no-error (add-msg m (add-typed-term-def v trm tp s))
process-def (Edefine v (Knd tp knd) e) s with check-type s empty-evctxt e tp knd
process-def (Edefine v (Knd tp knd) e) s | no-error m = no-error (add-msg m (add-kinded-type-def v tp knd s))
process-def (Edefine v (Knd tp knd) e) s | yes-error msg = yes-error ("While checking the definition of " ^ v ^ ":\n" ^ msg)
process-def (Kdefine v knd e) s = check-kind s empty-evctxt e knd ≫=err λ m → no-error (add-msg m (add-kind-def v knd s))

process-cmd : cmd → tpstate → error-t tpstate
process-cmd (DefCmd d) s = process-def d s
process-cmd (Echeck (Tp trm tp) e) s = check-term s empty-evctxt e trm tp ≫=err λ m → no-error (add-msg m s)
process-cmd (Echeck (Knd tp knd) e) s = check-type s empty-evctxt e tp knd ≫=err λ m → no-error (add-msg m s)
process-cmd (Kcheck k e) s = check-kind s empty-evctxt e k ≫=err λ m → no-error (add-msg m s)

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

