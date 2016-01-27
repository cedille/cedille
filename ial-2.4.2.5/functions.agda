module functions where

open import level
open import eq

{- Note that the Agda standard library has an interesting generalization
   of the following basic composition operator, with more dependent typing. -}

_∘_ : ∀{ℓ ℓ' ℓ''}{A : Set ℓ}{B : Set ℓ'}{C : Set ℓ''} →
      (B → C) → (A → B) → (A → C)
f ∘ g = λ x → f (g x)

∘-assoc : ∀{ℓ ℓ' ℓ'' ℓ'''}{A : Set ℓ}{B : Set ℓ'}{C : Set ℓ''}{D : Set ℓ'''}
           (f : C → D)(g : B → C)(h : A → B) → (f ∘ g) ∘ h ≡ f ∘ (g ∘ h)
∘-assoc f g h = refl

id : ∀{ℓ}{A : Set ℓ} → A → A
id = λ x → x

∘-id : ∀{ℓ ℓ'}{A : Set ℓ}{B : Set ℓ'}(f : A → B) → f ∘ id ≡ f
∘-id f = refl

id-∘ : ∀{ℓ ℓ'}{A : Set ℓ}{B : Set ℓ'}(f : A → B) → id ∘ f ≡ f
id-∘ f = refl

extensionality : {ℓ₁ ℓ₂ : Level} → Set (lsuc ℓ₁ ⊔ lsuc ℓ₂)
extensionality {ℓ₁}{ℓ₂} = ∀{A : Set ℓ₁}{B : Set ℓ₂}{f g : A → B} → (∀{a : A} → f a ≡ g a) → f ≡ g

record Iso {ℓ₁ ℓ₂ : Level} (A : Set ℓ₁) (B : Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
 constructor isIso
 field
   l-inv : A → B
   r-inv : B → A
   l-cancel : r-inv ∘ l-inv ≡ id
   r-cancel : l-inv ∘ r-inv ≡ id 
