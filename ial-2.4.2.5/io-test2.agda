module io-test2 where

open import io
open import list
open import string
open import unit

main : IO ⊤
main = getArgs >>= cont
          where cont : 𝕃 string → IO ⊤ 
                cont [] = return triv
                cont (x :: xs) = (readFiniteFile x) >>= putStr

