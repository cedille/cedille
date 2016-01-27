module eq where

open import level

----------------------------------------------------------------------
-- datatypes
----------------------------------------------------------------------

data _≡_ {ℓ} {A : Set ℓ} (x : A) : A → Set ℓ where
  refl : x ≡ x

{-# BUILTIN EQUALITY _≡_ #-}
{-# BUILTIN REFL refl #-}

----------------------------------------------------------------------
-- syntax
----------------------------------------------------------------------

infix 4 _≡_ 

----------------------------------------------------------------------
-- operations
----------------------------------------------------------------------

sym : ∀ {ℓ}{A : Set ℓ}{x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {ℓ}{A : Set ℓ}{x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

cong : ∀ {ℓ ℓ'}{A : Set ℓ}{B : Set ℓ'}(p : A → B) {x y : A} → x ≡ y → p x ≡ p y
cong p refl = refl

congf : ∀{l l' : Level}{A : Set l}{B : Set l'}{f f' : A → B}{b c : A} → f ≡ f' → b ≡ c → (f b) ≡ (f' c)
congf refl refl = refl

congf2 : ∀{l l' l'' : Level}{A : Set l}{B : Set l'}{C : Set l''}{f f' : A → B → C}{b c : A}{d e : B} → f ≡ f' → b ≡ c → d ≡ e → (f b d) ≡ (f' c e)
congf2 refl refl refl = refl

cong2 : ∀{i j k}{A : Set i}{B : Set j}{C : Set k}{a a' : A}{b b' : B}
  → (f : A → B → C)
  → a ≡ a' 
  → b ≡ b'
  → f a b ≡ f a' b'
cong2 f refl refl = refl

cong3 : ∀{i j k l}{A : Set i}{B : Set j}{C : Set k}{D : Set l}{a a' : A}{b b' : B}{c c' : C}
  → (f : A → B → C → D)
  → a ≡ a' 
  → b ≡ b'
  → c ≡ c'
  → f a b c ≡ f a' b' c'
cong3 f refl refl refl = refl
