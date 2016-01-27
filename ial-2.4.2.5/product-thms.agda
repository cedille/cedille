module product-thms where

open import eq
open import level
open import product
open import unit
open import functions

-- this is called the inspect idiom, in the Agda stdlib
keep : ∀{ℓ}{A : Set ℓ} → (x : A) → Σ A (λ y → x ≡ y)
keep x = ( x , refl )

,inj : ∀{ℓ ℓ'}{A : Set ℓ}{B : Set ℓ'}{a a' : A}{b b' : B} → 
        a , b ≡ a' , b' → a ≡ a' ∧ b ≡ b'
,inj refl = refl , refl

eta-× : ∀{ℓ₁ ℓ₂ ℓ₃}{A : Set ℓ₁}{B : Set ℓ₂}{C : Set ℓ₃}{h : A × B → C}
  → (extensionality {ℓ₁ ⊔ ℓ₂}{ℓ₃})
  → (λ c → h (fst c , snd c)) ≡ h
eta-× {A = A}{B}{C}{h} ext = ext eta-×-aux
 where
   eta-×-aux : ∀{a : Σ A (λ x → B)} → h (fst a , snd a) ≡ h a
   eta-×-aux {(a , b)} = refl

eq-× : ∀{ℓ₁ ℓ₂}{A : Set ℓ₁}{B : Set ℓ₂}{a a' : A}{b b' : B}
  → a ≡ a'
  → b ≡ b'
  → (a , b) ≡ (a' , b')
eq-× refl refl = refl

-- This module proves typical isomorphisms about ∧.
module ∧-Isos where
  postulate ext-set : ∀{l1 l2 : level} → extensionality {l1} {l2}
  
  ∧-unit-l : ∀{ℓ}{A : Set ℓ} → A → A ∧ ⊤
  ∧-unit-l x = x , triv

  ∧-unit-r : ∀{ℓ}{A : Set ℓ} → A → ⊤ ∧ A
  ∧-unit-r x = twist-× (∧-unit-l x)

  ∧-unit-l-iso : ∀{ℓ}{A : Set ℓ} → Iso A (A ∧ ⊤)
  ∧-unit-l-iso {_}{A} = isIso ∧-unit-l fst refl (ext-set aux)
   where
    aux : {a : A ∧ ⊤} → (fst a , triv) ≡ a
    aux {x , triv} = refl

  ∧-unit-r-iso : ∀{ℓ}{A : Set ℓ} → Iso A (⊤ ∧ A)
  ∧-unit-r-iso {_}{A} = isIso ∧-unit-r snd refl (ext-set aux)
   where
    aux : {a : ⊤ ∧ A} → (triv , snd a) ≡ a
    aux {triv , x} = refl

  ∧-assoc₁ : ∀{ℓ}{A B C : Set ℓ} → (A ∧ (B ∧ C)) → ((A ∧ B) ∧ C)
  ∧-assoc₁ (a , b , c) = ((a , b) , c)

  ∧-assoc₂ : ∀{ℓ}{A B C : Set ℓ} → ((A ∧ B) ∧ C) → (A ∧ (B ∧ C))
  ∧-assoc₂ ((a , b) , c) = (a , b , c)

  ∧-assoc-iso : ∀{ℓ}{A B C : Set ℓ} → Iso (A ∧ (B ∧ C)) ((A ∧ B) ∧ C)
  ∧-assoc-iso {_}{A}{B}{C} = isIso ∧-assoc₁ ∧-assoc₂ (ext-set aux₁) (ext-set aux₂)
   where
    aux₁ : {a : A ∧ (B ∧ C)} → ∧-assoc₂ (∧-assoc₁ a) ≡ a
    aux₁ {a , (b , c)} = refl

    aux₂ : {a : (A ∧ B) ∧ C} → ∧-assoc₁ (∧-assoc₂ a) ≡ a
    aux₂ {(a , b) , c} = refl
