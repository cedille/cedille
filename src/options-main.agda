module options-main where

import parse
open import general-util
open import lib
open import options-types
import options

module parsem = parse options.gratr2-nt ptr
open parsem
open parsem.pnoderiv options.rrs options.options-rtn
open import run ptr
open noderiv {- from run.agda -}

process-start : start → string
process-start s = ""

process : Run → string
process (ParseTree (parsed-start p) :: []) = process-start p
process r = "Parsing failure (run with -" ^ "-showParsed)."

putStrRunIf : 𝔹 → Run → IO ⊤
putStrRunIf tt r = putStrLn (Run-to-string r)
putStrRunIf ff r = return triv

processArgs : (showRun : 𝔹) → (showParsed : 𝔹) → 𝕃 string → IO ⊤ 
processArgs showRun showParsed (input-filename :: []) = (readFiniteFile input-filename) >>= processText
  where processText : string → IO ⊤
        processText x with runRtn (string-to-𝕃char x)
        processText x | s with s
        processText x | s | inj₁ cs = putStrLn ("Characters left before failure : " ^ (𝕃char-to-string cs)) >> putStrLn "Cannot proceed to parsing."
        processText x | s | inj₂ r with putStrRunIf showRun r | rewriteRun r
        processText x | s | inj₂ r | sr | r' with putStrRunIf showParsed r'
        processText x | s | inj₂ r | sr | r' | sr' = sr >> sr' >> putStrLn (process r')
                                     
processArgs showRun showParsed ("--showRun" :: xs) = processArgs tt showParsed xs 
processArgs showRun showParsed ("--showParsed" :: xs) = processArgs showRun tt xs 
processArgs showRun showParsed (x :: xs) = putStrLn ("Unknown option " ^ x)
processArgs showRun showParsed [] = putStrLn "Please run with the name of a file to process."

main : IO ⊤
main = getArgs >>= processArgs ff ff

