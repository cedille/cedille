module maybe-thms where

open import eq
open import level
open import maybe
open import product
open import sum

maybe-dec : ∀ {ℓ}{A : Set ℓ}(x : maybe A) → x ≡ nothing ∨ Σ A (λ a → x ≡ just a)
maybe-dec nothing = inj₁ refl
maybe-dec (just a) = inj₂ (a , refl)