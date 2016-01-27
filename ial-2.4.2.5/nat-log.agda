module nat-log where

open import bool
open import eq
open import nat
open import nat-thms
open import nat-division
open import product

data log-result (x : ℕ)(b : ℕ) : Set where
  pos-power : (e : ℕ) → (s : ℕ) → b pow e + s ≡ x → log-result x b
  no-power : x < b ≡ tt → log-result x b

-- as a first version, we do not try to prove termination of this function
{-# NO_TERMINATION_CHECK #-}
log : (x : ℕ) → (b : ℕ) → x =ℕ 0 ≡ ff → b =ℕ 0 ≡ ff → log-result x b
log x b p1 p2 with x ÷ b ! p2
log x b p1 p2 | 0 , r , u1 , u2 rewrite u1 = no-power u2
log x b p1 p2 | (suc q) , r , u1 , u2 with log (suc q) b refl p2
log x b p1 p2 | (suc q) , r , u1 , u2 | no-power u rewrite sym u1 = 
  pos-power 1 (b * q + r) lem 
  where lem : b * 1 + (b * q + r) ≡ b + q * b + r
        lem rewrite *1{b} | *comm b q = +assoc b (q * b) r
log x b p1 p2 | (suc q) , r , u1 , u2 | pos-power e s u rewrite sym u1 = 
  pos-power (suc e) (b * s + r) lem 
  where lem : b * b pow e + (b * s + r) ≡ b + q * b + r
        lem rewrite +assoc (b * b pow e) (b * s) r | sym (*distribl b (b pow e) s) | *comm b (b pow e + s) = 
          sym (cong (λ i → i * b + r) (sym u))

