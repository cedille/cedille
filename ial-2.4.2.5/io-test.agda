module io-test where

open import io
open import string
open import unit

main : IO ⊤
main = (readFiniteFile "hello-world.txt") >>= λ x → writeFile "output.txt" x

