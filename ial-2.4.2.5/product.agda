module product where

open import level

----------------------------------------------------------------------
-- types
----------------------------------------------------------------------

data Σ {ℓ ℓ'} (A : Set ℓ) (B : A → Set ℓ') : Set (ℓ ⊔ ℓ') where
  _,_ : (a : A) → (b : B a) → Σ A B

data Σi {ℓ ℓ'} (A : Set ℓ) (B : A → Set ℓ') : Set (ℓ ⊔ ℓ') where
  ,_ : {a : A} → (b : B a) → Σi A B

_×_ : ∀ {ℓ ℓ'} (A : Set ℓ) (B : Set ℓ') → Set (ℓ ⊔ ℓ')
A × B = Σ A (λ x → B)

_i×_ : ∀ {ℓ ℓ'} (A : Set ℓ) (B : Set ℓ') → Set (ℓ ⊔ ℓ')
A i× B = Σi A (λ x → B)

----------------------------------------------------------------------
-- syntax
----------------------------------------------------------------------

infix 2 Σ-syntax
infixr 3 _×_ _i×_ _∧_
infixr 4 _,_ 
infix  4 ,_

-- This provides the syntax: Σ[ x ∈ A ] B it is taken from the Agda
-- standard library. This style is nice when working in Set.
Σ-syntax : ∀ {a b} (A : Set a) → (A → Set b) → Set (a ⊔ b)
Σ-syntax = Σ

syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

----------------------------------------------------------------------
-- operations
----------------------------------------------------------------------
fst : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → A × B → A
fst (a , b) = a

snd : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → A × B → B
snd (a , b) = b

⟨_,_⟩ : ∀{ℓ₁ ℓ₂ ℓ₃ ℓ₄}
         {A : Set ℓ₁}{B : Set ℓ₂}
         {C : Set ℓ₃}{D : Set ℓ₄}
       → (A → C)
       → (B → D)
       → (A × B → C × D)
⟨ f , g ⟩ (a , b) = f a , g b

twist-× : ∀{ℓ₁ ℓ₂}
     {A : Set ℓ₁}{B : Set ℓ₂}
    → A × B
    → B × A
twist-× (a , b) = (b , a)       

rl-assoc-× : ∀{ℓ₁ ℓ₂ ℓ₃}
             {A : Set ℓ₁}{B : Set ℓ₂}
             {C : Set ℓ₃}
           → A × (B × C)
           → (A × B) × C
rl-assoc-× (a , b , c) =  ((a , b) , c)

lr-assoc-× : ∀{ℓ₁ ℓ₂ ℓ₃}
             {A : Set ℓ₁}{B : Set ℓ₂}
             {C : Set ℓ₃}
           → (A × B) × C
           → A × (B × C)
lr-assoc-× ((a , b) , c) = (a , b , c)

----------------------------------------------------------------------
-- some logical notation
----------------------------------------------------------------------
_∧_ : ∀ {ℓ ℓ'} (A : Set ℓ) (B : Set ℓ') → Set (ℓ ⊔ ℓ')
_∧_ = _×_

∃ : ∀ {ℓ ℓ'} (A : Set ℓ) (B : A → Set ℓ') → Set (ℓ ⊔ ℓ')
∃ = Σ

∃i : ∀ {ℓ ℓ'} (A : Set ℓ) (B : A → Set ℓ') → Set (ℓ ⊔ ℓ')
∃i = Σi

