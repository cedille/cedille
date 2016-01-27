module huffman-main where

import parse
open import lib
open import huffman-types
import huffman

module parsem = parse huffman.gratr2-nt ptr
open parsem
open parsem.pnoderiv huffman.rrs huffman.huffman-rtn
open import run ptr
open noderiv {- from run.agda -}

process-start : start → string
process-start s = ""

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

