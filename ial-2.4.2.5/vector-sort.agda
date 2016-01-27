module vector-sort where

open import level
open import bool
open import nat
open import product
open import vector

insert𝕍 : ∀{ℓ}{A : Set ℓ}{n : ℕ} → (_<_ : A → A → 𝔹) → (_≅_ : A → A → 𝔹) → A → 𝕍 A n → Σi ℕ (λ m → 𝕍 A (suc m))
insert𝕍 _<_ _≅_ x [] = , [ x ]𝕍
insert𝕍 _<_ _≅_ x (y :: ys) with x < y
... | tt = , x :: y :: ys
... | ff with x ≅ y 
... | tt = , y :: ys
... | ff with (insert𝕍 _<_ _≅_ x ys)
... | , r = , y :: r

insertion-sort𝕍 : ∀{ℓ}{A : Set ℓ}{n : ℕ} → (_<_ : A → A → 𝔹) → (_≅_ : A → A → 𝔹) → 𝕍 A (suc n) → Σi ℕ (λ m → 𝕍 A (suc m))
insertion-sort𝕍 _ _ (x :: []) = , [ x ]𝕍
insertion-sort𝕍 _<_ _≅_ (x :: (y :: ys)) with insertion-sort𝕍 _<_ _≅_ (y :: ys)
... | , (z :: zs) = insert𝕍 _<_ _≅_ x (z :: zs)

test-insertion-sort𝕍 = insertion-sort𝕍 _<_ _=ℕ_ (3 :: 5 :: 2 :: 7 :: 1 :: 2 :: 3 :: 9 :: [])
