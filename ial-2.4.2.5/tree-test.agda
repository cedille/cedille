module tree-test where

open import tree
open import nat
open import bool
open import bool-to-string
open import list

test-tree = node 2 ( (leaf 3) :: (node 4 ( (leaf 5) :: (leaf 7) :: [] )) :: (leaf 6) :: (leaf 7) :: [])

perfect3 = perfect-binary-tree 3 tt

perfect3-string = 𝕋-to-string 𝔹-to-string perfect3