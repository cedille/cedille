-- an example showing how to use sigma types to define a type for non-zero natural numbers
module nat-nonzero where

open import bool
open import eq
open import nat
open import nat-thms
open import product

ℕ⁺ : Set
ℕ⁺ = Σ ℕ (λ n → iszero n ≡ ff)

suc⁺ : ℕ⁺ → ℕ⁺ 
suc⁺ (x , p) = (suc x , refl)

_+⁺_ : ℕ⁺ → ℕ⁺ → ℕ⁺
(x , p) +⁺ (y , q) = x + y , iszerosum2 x y p

_*⁺_ : ℕ⁺ → ℕ⁺ → ℕ⁺
(x , p) *⁺ (y , q) = (x * y , iszeromult x y p q)
