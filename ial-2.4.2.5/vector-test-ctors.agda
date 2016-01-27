module vector-test-ctors where

open import bool
open import list
open import vector

----------------------------------------------------------------------
-- syntax
----------------------------------------------------------------------

test-vector : 𝕃 (𝕍 𝔹 2)
test-vector = (ff :: tt :: []) :: (tt :: ff :: []) :: (tt :: ff :: []) :: []



