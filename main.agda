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

--process-cmd : cmd → IO string

process-cmds : cmds → IO ⊤
process-cmds (CmdsNext c cs) = {!!}
process-cmds (CmdsStart c) = process-cmd c

process-start : start → IO ⊤
process-start (Cmds cs) = process-cmds cs

processFile : string → IO ⊤
processFile input-filename = (readFiniteFile input-filename) >>= processText
  where processText : string → IO ⊤
        processText x with runRtn (string-to-𝕃char x)
        processText x | inj₁ cs = 
           putStr ("In file \"" ^ input-filename ^ "\":") >>
           putStr "Characters left before failure : " >> putStr (𝕃char-to-string cs) >> putStr "\nCannot proceed to parsing.\n" 
        processText x | inj₂ r with rewriteRun r
        processText x | inj₂ r | (ParseTree (parsed-start p) :: []) = process-start p 
        processText x | inj₂ r | _ = putStr ("Parse error in file \"" ^ x ^ "\"\n") 

processArgs : 𝕃 string → IO ⊤ 
processArgs (input-filename :: []) = (processFile input-filename)
processArgs (x :: xs) = putStr ("Unknown option " ^ x ^ "\n")
processArgs [] = putStr "Please run with the name of a file to process.\n"

main : IO ⊤
main = getArgs >>= processArgs 

