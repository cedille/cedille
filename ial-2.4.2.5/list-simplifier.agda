module list-simplifier where

open import level
open import bool
open import functions
open import eq
open import empty
open import level
open import list
open import list-thms
open import nat
open import neq
open import product
open import product-thms

data 𝕃ʳ : Set → Set lone where
  _ʳ : {A : Set} → 𝕃 A → 𝕃ʳ A
  _++ʳ_ : {A : Set} → 𝕃ʳ A → 𝕃ʳ A → 𝕃ʳ A
  mapʳ : {A B : Set} → (A → B) → 𝕃ʳ A → 𝕃ʳ B
  _::ʳ_ : {A : Set} → A → 𝕃ʳ A → 𝕃ʳ A
  []ʳ : {A : Set} → 𝕃ʳ A

𝕃⟦_⟧ : {A : Set} → 𝕃ʳ A → 𝕃 A
𝕃⟦ l ʳ ⟧ = l
𝕃⟦ t1 ++ʳ t2 ⟧ = 𝕃⟦ t1 ⟧ ++ 𝕃⟦ t2 ⟧
𝕃⟦ mapʳ f t ⟧ = map f 𝕃⟦ t ⟧ 
𝕃⟦ x ::ʳ t ⟧ = x :: 𝕃⟦ t ⟧ 
𝕃⟦ []ʳ ⟧ = []

is-emptyʳ : {A : Set} → 𝕃ʳ A → 𝔹
is-emptyʳ []ʳ = tt
is-emptyʳ _ = ff

is-emptyʳ-≡ : {A : Set}(t : 𝕃ʳ A) → is-emptyʳ t ≡ tt → t ≡ []ʳ 
is-emptyʳ-≡ []ʳ p = refl
is-emptyʳ-≡ (_ ++ʳ _) ()
is-emptyʳ-≡ (mapʳ _ _) ()
is-emptyʳ-≡ (_ ::ʳ _) ()
is-emptyʳ-≡ (_ ʳ) ()

𝕃ʳ-simp-step : {A : Set}(t : 𝕃ʳ A) → 𝕃ʳ A
𝕃ʳ-simp-step ((t1a ++ʳ t1b) ++ʳ t2) = t1a ++ʳ (t1b ++ʳ t2) 
𝕃ʳ-simp-step ((x ::ʳ t1) ++ʳ t2) = x ::ʳ (t1 ++ʳ t2) 
𝕃ʳ-simp-step ([]ʳ ++ʳ t2) = t2 
𝕃ʳ-simp-step ((l ʳ) ++ʳ t2) = 
  if is-emptyʳ t2 then l ʳ else ((l ʳ) ++ʳ t2)
𝕃ʳ-simp-step ((mapʳ f t1) ++ʳ t2) = 
  if is-emptyʳ t2 then mapʳ f t1 else ((mapʳ f t1) ++ʳ t2)
𝕃ʳ-simp-step (mapʳ f (t1 ++ʳ t2)) = (mapʳ f t1) ++ʳ (mapʳ f t2) 
𝕃ʳ-simp-step (mapʳ f (l ʳ)) = (map f l) ʳ 
𝕃ʳ-simp-step (mapʳ f (mapʳ g t)) = mapʳ (f ∘ g) t 
𝕃ʳ-simp-step (mapʳ f (x ::ʳ t)) = (f x) ::ʳ (mapʳ f t)
𝕃ʳ-simp-step (mapʳ f []ʳ) = []ʳ 
𝕃ʳ-simp-step (l ʳ) = l ʳ 
𝕃ʳ-simp-step (x ::ʳ t) = (x ::ʳ t)
𝕃ʳ-simp-step []ʳ = []ʳ 

𝕃ʳ-simp-sdev : {A : Set}(t : 𝕃ʳ A) → 𝕃ʳ A
𝕃ʳ-simp-sdev (l ʳ) = (l ʳ)
𝕃ʳ-simp-sdev (t1 ++ʳ t2) = 𝕃ʳ-simp-step ((𝕃ʳ-simp-sdev t1) ++ʳ (𝕃ʳ-simp-sdev t2))
𝕃ʳ-simp-sdev (mapʳ f t1) = 𝕃ʳ-simp-step (mapʳ f (𝕃ʳ-simp-sdev t1))
𝕃ʳ-simp-sdev (x ::ʳ t1) = 𝕃ʳ-simp-step (x ::ʳ (𝕃ʳ-simp-sdev t1))
𝕃ʳ-simp-sdev []ʳ = []ʳ 

𝕃ʳ-simp : {A : Set}(t : 𝕃ʳ A) → ℕ → 𝕃ʳ A
𝕃ʳ-simp t 0 = t
𝕃ʳ-simp t (suc n) = 𝕃ʳ-simp-sdev (𝕃ʳ-simp t n)

𝕃ʳ-simp-step-sound : {A : Set}(t : 𝕃ʳ A) → 𝕃⟦ t ⟧ ≡ 𝕃⟦ 𝕃ʳ-simp-step t ⟧
𝕃ʳ-simp-step-sound ((t1a ++ʳ t1b) ++ʳ t2) = ++-assoc 𝕃⟦ t1a ⟧ 𝕃⟦ t1b ⟧ 𝕃⟦ t2 ⟧
𝕃ʳ-simp-step-sound ((x ::ʳ t1) ++ʳ t2) = refl
𝕃ʳ-simp-step-sound ([]ʳ ++ʳ t2) = refl
𝕃ʳ-simp-step-sound ((l ʳ) ++ʳ t2) with keep (is-emptyʳ t2)
𝕃ʳ-simp-step-sound ((l ʳ) ++ʳ t2) | tt , p rewrite p | is-emptyʳ-≡ t2 p | ++[] l = refl
𝕃ʳ-simp-step-sound ((l ʳ) ++ʳ t2) | ff , p rewrite p = refl
𝕃ʳ-simp-step-sound ((mapʳ f t1) ++ʳ t2) with keep (is-emptyʳ t2)
𝕃ʳ-simp-step-sound ((mapʳ f t1) ++ʳ t2) | tt , p rewrite p | is-emptyʳ-≡ t2 p | ++[] (map f 𝕃⟦ t1 ⟧) = refl
𝕃ʳ-simp-step-sound ((mapʳ f t1) ++ʳ t2) | ff , p rewrite p = refl
𝕃ʳ-simp-step-sound (l ʳ) = refl
𝕃ʳ-simp-step-sound (mapʳ f (t1 ++ʳ t2)) = map-append f 𝕃⟦ t1 ⟧ 𝕃⟦ t2 ⟧
𝕃ʳ-simp-step-sound (mapʳ f (l ʳ)) = refl
𝕃ʳ-simp-step-sound (mapʳ f (mapʳ g t)) = map-compose f g 𝕃⟦ t ⟧
𝕃ʳ-simp-step-sound (mapʳ f (x ::ʳ t)) = refl
𝕃ʳ-simp-step-sound (mapʳ f []ʳ) = refl
𝕃ʳ-simp-step-sound (x ::ʳ t) = refl
𝕃ʳ-simp-step-sound []ʳ = refl

𝕃ʳ-simp-sdev-sound : {A : Set}(t : 𝕃ʳ A) → 𝕃⟦ t ⟧ ≡ 𝕃⟦ 𝕃ʳ-simp-sdev t ⟧
𝕃ʳ-simp-sdev-sound (l ʳ) = refl
𝕃ʳ-simp-sdev-sound (t1 ++ʳ t2) 
  rewrite sym (𝕃ʳ-simp-step-sound ((𝕃ʳ-simp-sdev t1) ++ʳ (𝕃ʳ-simp-sdev t2))) | 𝕃ʳ-simp-sdev-sound t1 | 𝕃ʳ-simp-sdev-sound t2 = refl
𝕃ʳ-simp-sdev-sound (mapʳ f t1)
  rewrite sym (𝕃ʳ-simp-step-sound (mapʳ f (𝕃ʳ-simp-sdev t1))) | 𝕃ʳ-simp-sdev-sound t1 = refl
𝕃ʳ-simp-sdev-sound (x ::ʳ t1) rewrite 𝕃ʳ-simp-sdev-sound t1 = refl
𝕃ʳ-simp-sdev-sound []ʳ = refl

𝕃ʳ-simp-sound : {A : Set}(t : 𝕃ʳ A)(n : ℕ) → 𝕃⟦ t ⟧ ≡ 𝕃⟦ 𝕃ʳ-simp t n ⟧
𝕃ʳ-simp-sound t 0 = refl
𝕃ʳ-simp-sound t (suc n) rewrite sym (𝕃ʳ-simp-sdev-sound (𝕃ʳ-simp t n)) = 𝕃ʳ-simp-sound t n

module test1 {A B : Set}(f : A → B)(l1 l2 : 𝕃 A) where

  lhs = (mapʳ f (l1 ʳ)) ++ʳ (mapʳ f (l2 ʳ))

  rhs = mapʳ f ((l1 ʳ) ++ʳ (l2 ʳ))

  test-tp : Set
  test-tp = 𝕃⟦ lhs ⟧ ≡ 𝕃⟦ rhs ⟧

  test : test-tp
  test rewrite (𝕃ʳ-simp-sdev-sound rhs) = refl

module test2 {A B : Set}(f : A → B)(l1 l2 l3 : 𝕃 A) where

  lhs = mapʳ f (((l1 ʳ) ++ʳ (l2 ʳ)) ++ʳ (l3 ʳ))

  rhs = 𝕃ʳ-simp lhs 3

  test-tp : Set
  test-tp = 𝕃⟦ lhs ⟧ ≡ 𝕃⟦ rhs ⟧

  test : test-tp
  test = 𝕃ʳ-simp-sound lhs 3

  one-step : 𝕃ʳ B
  one-step = 𝕃ʳ-simp-step lhs

  sdev : 𝕃ʳ B
  sdev = 𝕃ʳ-simp-sdev lhs


