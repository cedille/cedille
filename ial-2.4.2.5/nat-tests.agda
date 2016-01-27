module nat-tests where

open import eq
open import nat
open import nat-division
open import nat-to-string
open import product

{- you can prove x + 0 ≡ x and 0 + x ≡ x without induction, if you
   use this more verbose definition of addition: -}
_+a_ : ℕ → ℕ → ℕ
0 +a 0 = 0
(suc x) +a 0 = (suc x)
0 +a (suc y) = (suc y)
(suc x) +a (suc y) = suc (suc (x +a y))

0+a : ∀ (x : ℕ) → x +a 0 ≡ x
0+a 0 = refl
0+a (suc y) = refl

+a0 : ∀ (x : ℕ) → 0 +a x ≡ x
+a0 0 = refl
+a0 (suc y) = refl

8-div-3-lem : 8 ÷ 3 !! refl ≡ 2 , 2
8-div-3-lem = refl

23-div-5-lem : 23 ÷ 5 !! refl ≡ 4 , 3 
23-div-5-lem = refl

ℕ-to-string-lem : ℕ-to-string 237 ≡ "237"
ℕ-to-string-lem = refl

