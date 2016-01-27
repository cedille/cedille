-- modular arithmetic

module nat-mod where

open import eq
open import nat

infix 8 _≡_mod_

data _≡_mod_ : ℕ → ℕ → ℕ → Set where
  mod-refl : ∀ {n k} → n ≡ n mod k
  mod-add : ∀ {n m k} → n ≡ m mod k → n + k ≡ m mod k
  mod-symm : ∀ {n m k} → n ≡ m mod k → m ≡ n mod k

{-
mod-trans : ∀ {n m o k} → n ≡ m mod k → m ≡ o mod k → n ≡ o mod k
mod-trans{n}{.n}{o}{k} mod-refl p2 = {!!}
mod-trans}{m}{o}{k} (mod-add p1) p2 = {!!}
mod-trans{n}{m}{o}{k} (mod-symm p1) p2 = {!!}
-}