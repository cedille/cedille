module sum where

open import level
open import bool
open import eq
open import maybe
open import product

----------------------------------------------------------------------
-- datatypes
----------------------------------------------------------------------

data _⊎_ {ℓ ℓ'} (A : Set ℓ) (B : Set ℓ') : Set (ℓ ⊔ ℓ') where
  inj₁ : (x : A) → A ⊎ B
  inj₂ : (y : B) → A ⊎ B

_∨_ : ∀ {ℓ ℓ'} (A : Set ℓ) (B : Set ℓ') → Set (ℓ ⊔ ℓ')
_∨_ = _⊎_

----------------------------------------------------------------------
-- syntax
----------------------------------------------------------------------

infixr 1 _⊎_ _∨_

----------------------------------------------------------------------
-- operations
----------------------------------------------------------------------

_≫=⊎_ : ∀ {ℓ ℓ'}{A : Set ℓ}{B : Set ℓ'}{C : Set (ℓ ⊔ ℓ')}  → A ⊎ B → (B → A ⊎ C) → A ⊎ C
inj₁ x ≫=⊎ f = inj₁ x
inj₂ x ≫=⊎ f = f x

return⊎ : ∀ {ℓ ℓ'}{A : Set ℓ}{B : Set ℓ'} → B → A ⊎ B
return⊎ b = inj₂ b

infix 5 error⊎_

error⊎_ : ∀ {ℓ ℓ'}{A : Set ℓ}{B : Set ℓ'} → A → A ⊎ B
error⊎_ a = inj₁ a

extract-inj₁≡ : ∀{ℓ}{ℓ'}{A : Set ℓ}{B : Set ℓ'}{a a' : A} → inj₁{B = B} a ≡ inj₁ a' → a ≡ a'
extract-inj₁≡ refl = refl

extract-inj₂≡ : ∀{ℓ}{ℓ'}{A : Set ℓ}{B : Set ℓ'}{b b' : B} → inj₂{A = A} b ≡ inj₂ b' → b ≡ b'
extract-inj₂≡ refl = refl

=⊎ : ∀{ℓ}{ℓ'}{A : Set ℓ}{B : Set ℓ'} → (A → A → 𝔹) → (B → B → 𝔹) → A ⊎ B → A ⊎ B → 𝔹
=⊎ eqa eqb (inj₁ a) (inj₁ a') = eqa a a'
=⊎ eqa eqb (inj₂ b) (inj₂ b') = eqb b b'
=⊎ _ _ _ _ = ff


=⊎-to-≡ : ∀{ℓ}{ℓ'}{A : Set ℓ}{B : Set ℓ'} → (_eqa_ : A → A → 𝔹) → (_eqb_ : B → B → 𝔹) → ((a a' : A) → (a eqa a' ≡ tt) → a ≡ a') → ((b b' : B) → (b eqb b' ≡ tt) → b ≡ b') →  (x y : A ⊎ B) → =⊎ _eqa_ _eqb_ x y  ≡ tt → x ≡ y 
=⊎-to-≡ eqa eqb risea riseb (inj₁ a) (inj₁ a') p rewrite risea a a' p = refl
=⊎-to-≡ eqa eqb risea riseb (inj₂ b) (inj₂ b') p rewrite riseb b b' p = refl
=⊎-to-≡ eqa eqb risea riseb (inj₁ a) (inj₂ b) ()
=⊎-to-≡ eqa eqb risea riseb (inj₂ b) (inj₁ a) ()




≡⊎-to-= : ∀{ℓ}{ℓ'}{A : Set ℓ}{B : Set ℓ'} → (_eqa_ : A → A → 𝔹) → (_eqb_ : B → B → 𝔹) → ((a a' : A) → a ≡ a' → a eqa a' ≡ tt) → ((b b' : B) → b ≡ b' → b eqb b' ≡ tt) →  (x y : A ⊎ B) → x ≡ y → =⊎ _eqa_ _eqb_ x y  ≡ tt
≡⊎-to-= eqa eqb dropa dropb (inj₁ a) (inj₁ a') p = dropa a a' (extract-inj₁≡ p)
≡⊎-to-= eqa eqb dropa dropb (inj₂ b) (inj₂ b') p = dropb b b' (extract-inj₂≡ p)
≡⊎-to-= eqa eqb dropa dropb (inj₁ a) (inj₂ b) ()
≡⊎-to-= eqa eqb dropa dropb (inj₂ b) (inj₁ a) ()
