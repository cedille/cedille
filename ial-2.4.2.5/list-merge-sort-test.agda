module list-merge-sort-test where

open import list
open import nat

open import list-merge-sort ℕ _<_

test-list = 3 :: 2 :: 5 :: 1 :: 1 :: 6 :: 8 :: 9 :: 4 :: []

sorted = merge-sort test-list