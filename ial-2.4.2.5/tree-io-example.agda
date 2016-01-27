module tree-io-example where

open import io
open import list
open import maybe
open import string
open import tree
open import unit
open import nat-to-string

errmsg = "Run with a single (small) number as the command-line argument.\n"

processArgs : 𝕃 string → IO ⊤ 
processArgs (s :: []) with string-to-ℕ s 
... | nothing = putStr errmsg
... | just n = putStr (𝕋-to-string ℕ-to-string (perfect-binary-tree n n)) >> putStr "\n"
processArgs _ = putStr errmsg

main : IO ⊤
main = getArgs >>= processArgs 

