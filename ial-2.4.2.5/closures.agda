open import bool
open import level
open import eq
open import product
open import product-thms
open import relations 

module closures where

  module basics {ℓ ℓ' : level}{A : Set ℓ} (_>A_ : A → A → Set ℓ') where

    data tc : A → A → Set (ℓ ⊔ ℓ') where
      tc-step : ∀{a b : A} → a >A b → tc a b
      tc-trans : ∀{a b c : A} → tc a b → tc b c → tc a c

    data rc : A → A → Set (ℓ ⊔ ℓ') where
      rc-step : ∀{a b : A} → a >A b → rc a b
      rc-refl : ∀{a : A} → rc a a
  
    tc-transitive : transitive tc
    tc-transitive = tc-trans 

  module combinations {ℓ ℓ' : level}{A : Set ℓ} (_>A_ : A → A → Set ℓ') where
     open basics public

     rtc : A → A → Set (ℓ ⊔ ℓ')
     rtc = rc (tc _>A_)

     rtc-refl : reflexive rtc
     rtc-refl = rc-refl

     rtc-trans : transitive rtc
     rtc-trans (rc-step{a}{b} x) (rc-step{.b}{c} x') = rc-step (tc-trans x x')
     rtc-trans (rc-step x) rc-refl = rc-step x
     rtc-trans rc-refl (rc-step x) = rc-step x
     rtc-trans rc-refl rc-refl = rc-refl

