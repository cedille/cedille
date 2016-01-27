module unit where

open import level
open import eq

data ⊤ : Set where
  triv : ⊤

{-# COMPILED_DATA ⊤ () ()  #-}

single-range : ∀{U : Set}{g : U → ⊤} → ∀{u : U} → g u ≡ triv
single-range {U}{g}{u} with g u
... | triv = refl
