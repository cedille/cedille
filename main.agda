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

data tpstate : Set where
  mk-tpstate : string → -- output for the user

               trie term → -- untyped term definitions

               trie (term × type) → -- typed term definitions

               trie (type × kind) → -- kinded type definitions

               trie kind → -- kind definitions

               tpstate

add-typed-term-def : var → term → type → tpstate → tpstate
add-typed-term-def v trm tp (mk-tpstate o d td yd kd) = (mk-tpstate o d (trie-insert td v (trm , tp)) yd kd)

add-kinded-type-def : var → type → kind → tpstate → tpstate
add-kinded-type-def v tp knd (mk-tpstate o d td yd kd) = (mk-tpstate o d td (trie-insert yd v (tp , knd)) kd)

add-kind-def : var → kind → tpstate → tpstate
add-kind-def v knd (mk-tpstate o d td yd kd) = (mk-tpstate o d td yd (trie-insert kd v knd))

check-term : tpstate → evidence → term → type → error-t ⊤  
check-type : tpstate → evidence → type → kind → error-t ⊤  
check-kind : tpstate → evidence → kind → error-t ⊤  
check-term s ev trm tp = yes-error "check-term not implemented"
check-type s ev tp knd = yes-error "check-type not implemented"
check-kind s ev knd = yes-error "check-kind not implemented"

process-cmd : cmd → tpstate → error-t tpstate
process-cmd (Tdefine v t) (mk-tpstate o d td yd kd) = no-error (mk-tpstate o (trie-insert d v t) td yd kd)
process-cmd (Edefine v (Tp trm tp) e) s = check-term s e trm tp ≫=err λ _ → no-error (add-typed-term-def v trm tp s)
process-cmd (Edefine v (Knd tp knd) e) s = check-type s e tp knd ≫=err λ _ → no-error (add-kinded-type-def v tp knd s)
process-cmd (Edefine v (Superknd knd) e) s = check-kind s e knd ≫=err λ _ → no-error (add-kind-def v knd s)

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

processArgs : (showRun : 𝔹) → (showParsed : 𝔹) → 𝕃 string → IO ⊤ 
processArgs showRun showParsed (input-filename :: []) = (readFiniteFile input-filename) >>= processText
  where processText : string → IO ⊤
        processText x with runRtn (string-to-𝕃char x)
        processText x | s with s
        processText x | s | inj₁ cs = putStr "Characters left before failure : " >> putStr (𝕃char-to-string cs) >> putStr "\nCannot proceed to parsing.\n"
        processText x | s | inj₂ r with putStrRunIf showRun r | rewriteRun r
        processText x | s | inj₂ r | sr | r' with putStrRunIf showParsed r'
        processText x | s | inj₂ r | sr | r' | sr' = sr >> sr' >> putStr (process r')
                                     
processArgs showRun showParsed ("--showRun" :: xs) = processArgs tt showParsed xs 
processArgs showRun showParsed ("--showParsed" :: xs) = processArgs showRun tt xs 
processArgs showRun showParsed (x :: xs) = putStr ("Unknown option " ^ x ^ "\n")
processArgs showRun showParsed [] = putStr "Please run with the name of a file to process.\n"

main : IO ⊤
main = getArgs >>= processArgs ff ff

