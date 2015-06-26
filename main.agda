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
open import syntax-util

process-cmd : cmd → tpstate → error-t tpstate
process-cmd (DefCmd d) s = check-def s d
process-cmd (Echeck (Tp trm tp) e e') s = 
 (check-type s empty-ctxt e' tp Star ≫check check-term s empty-ctxt e trm tp) ≫=err λ m → no-error (add-msg m s)
process-cmd (Echeck (Knd tp knd) e e') s = 
 (check-kind s empty-ctxt e' knd ≫check check-type s empty-ctxt e tp knd) ≫=err λ m → no-error (add-msg m s)
process-cmd (Kcheck k e) s = check-kind s empty-ctxt e k ≫=err λ m → no-error (add-msg m s)
process-cmd (Print x) s with lookup-var s x
process-cmd (Print x) s | tpstate-superkinding k = no-error (add-msg (x ^ " ∷ " ^ kind-to-string k ^ " ⇐ □\n") s)
process-cmd (Print x) s | tpstate-kinding tp k = no-error (add-msg (x ^ " ∷ " ^ type-to-string tp ^ " ⇐ " ^ kind-to-string k ^ "\n") s)
process-cmd (Print x) s | tpstate-typing trm tp = no-error (add-msg (x ^ " ∷ " ^ term-to-string trm ^ " ⇐ " ^ type-to-string tp ^ "\n") s)
process-cmd (Print x) s | tpstate-untyped trm = no-error (add-msg (x ^ " = " ^ term-to-string trm ^ "\n") s)
process-cmd (Print x) s | tpstate-nothing = no-error (add-msg (x ^ " is undefined.\n") s)
process-cmd (SynthTerm x t e) s with synth-term s empty-ctxt e t
process-cmd (SynthTerm x t e) s | no-error (m , tp) = no-error (add-msg m (add-typed-term-def x t tp s))
process-cmd (SynthTerm x t e) s | yes-error m = add-to-def-error x m 
process-cmd (SynthType x t e) s with synth-type s empty-ctxt e t
process-cmd (SynthType x t e) s | no-error (m , k) = no-error (add-msg m (add-kinded-type-def x t k s))
process-cmd (SynthType x t e) s | yes-error m = add-to-def-error x m


process-cmds : cmds → tpstate → error-t tpstate
process-cmds (CmdsStart c) s = process-cmd c s
process-cmds (CmdsNext c cs) s with process-cmd c s
process-cmds (CmdsNext c cs) s | no-error s' = process-cmds cs s'
process-cmds (CmdsNext c cs) s | yes-error m = let m' = get-output-msg s in
                                                 yes-error (m' ^ (newline-sep-if m' m) ^ m)

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

