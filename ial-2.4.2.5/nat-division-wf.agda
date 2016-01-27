module nat-division-wf where

open import bool
open import bool-thms
open import eq
open import neq
open import nat
open import nat-thms
open import product
open import product-thms
open import sum
open import termination

----------------------------------------------------------------------
-- syntax
----------------------------------------------------------------------

infixl 10 _÷_!_

----------------------------------------------------------------------
-- operations
----------------------------------------------------------------------

{- a div-result for dividend x and divisor d consists of the quotient q, remainder r, 
   a proof that q * d + r = x, and a proof that the remainder is less than the divisor. -}
div-result : ℕ → ℕ → Set 
div-result x d = Σ ℕ (λ q → Σ ℕ (λ r → q * d + r ≡ x ∧ r < d ≡ tt))

-- this uses well-founded recursion.  The approach in nat-division.agda is arguably simpler.
div-helper : ∀ (x : ℕ) → ↓𝔹 _>_ x → (d : ℕ) → d =ℕ 0 ≡ ff → div-result x d
div-helper x ↓x 0 () 
div-helper 0 (pf↓ fx) (suc d) _ = 0 , 0 , refl , refl
div-helper (suc x) (pf↓ fx) (suc d) _ with keep (x < d) 
div-helper (suc x) (pf↓ fx) (suc d) _ | tt , p = 0 , suc x , refl , p
div-helper (suc x) (pf↓ fx) (suc d) _ | ff , p 
  with div-helper (x ∸ d) (fx (∸<1 {x} {d})) (suc d) refl
div-helper (suc x) (pf↓ fx) (suc d) _ | ff , p | q , r , u , v = 
  suc q , r , lem{q * suc d} (∸eq-swap{x}{d}{q * suc d + r} (<ff{x} p) u) , v
  where lem : ∀ {a b c : ℕ} → a + b + c ≡ x → suc (c + a + b) ≡ suc x 
        lem{a}{b}{c} p' rewrite +comm c a | sym (+assoc a c b) 
                              | +comm c b | +assoc a b c | p' = refl

_÷_!_ : (x : ℕ) → (d : ℕ) → d =ℕ 0 ≡ ff → div-result x d
x ÷ d ! p = div-helper x (↓-> x) d p

_÷_!!_ : ℕ → (d : ℕ) → d =ℕ 0 ≡ ff → ℕ × ℕ
x ÷ d !! p with x ÷ d ! p
... | q , r , p' = q , r

-- return quotient only
_÷_div_ : ℕ → (d : ℕ) → d =ℕ 0 ≡ ff → ℕ 
x ÷ d div p with x ÷ d ! p
... | q , r , p' = q

