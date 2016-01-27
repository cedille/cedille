open import bool

module list-merge-sort (A : Set) (_<A_ : A → A → 𝔹) where

open import braun-tree A _<A_
open import eq
open import list
open import nat
open import nat-thms

merge : (l1 l2 : 𝕃 A) → 𝕃 A
merge [] ys = ys
merge xs [] = xs
merge (x :: xs) (y :: ys) with x <A y
merge (x :: xs) (y :: ys) | tt = x :: (merge xs (y :: ys))
merge (x :: xs) (y :: ys) | ff = y :: (merge (x :: xs) ys)

merge-sort-h : ∀{n : ℕ} → braun-tree' n → 𝕃 A
merge-sort-h (bt'-leaf a) = [ a ]
merge-sort-h (bt'-node l r p) = merge (merge-sort-h l) (merge-sort-h r)

merge-sort : 𝕃 A → 𝕃 A
merge-sort [] = []
merge-sort (a :: as) with 𝕃-to-braun-tree' a as
merge-sort (a :: as) | t = merge-sort-h t
