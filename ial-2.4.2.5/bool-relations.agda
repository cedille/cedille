{- This file describes properties of computable relations. -}

open import bool
open import level
open import eq
open import product
open import product-thms

module bool-relations {ℓ : level}{A : Set ℓ} (_≤A_ : A → A → 𝔹) where

reflexive : Set (ℓ)
reflexive = ∀ {a : A} → a ≤A a ≡ tt

transitive : Set (ℓ)
transitive = ∀ {a b c : A} → a ≤A b ≡ tt → b ≤A c ≡ tt → a ≤A c ≡ tt

total : Set ℓ
total = ∀ {a b : A} → a ≤A b ≡ ff → b ≤A a ≡ tt

total-reflexive : total → reflexive 
total-reflexive tot {a} with keep (a ≤A a)
total-reflexive tot {a} | tt , p = p
total-reflexive tot {a} | ff , p = tot p

_iso𝔹_ : A → A → 𝔹
d iso𝔹 d' = d ≤A d' && d' ≤A d

iso𝔹-intro : ∀{x y : A} → x ≤A y ≡ tt → y ≤A x ≡ tt → x iso𝔹 y ≡ tt
iso𝔹-intro p1 p2 rewrite p1 | p2 = refl


