module termination where

open import bool
open import eq
open import level
open import list
open import nat
open import nat-thms
open import product
open import sum

----------------------------------------------------------------------
-- types
----------------------------------------------------------------------

{- ↓ _>_ a means that the _>_ relation is well-founded below a.  That
   is, there are no infinite chains a > a1 > ... starting with a. 
   One can also say that _>_ terminates from a. -}
data ↓ {ℓ ℓ'} {A : Set ℓ} (_>_ : A → A → Set ℓ') : A → Set (ℓ ⊔ ℓ') where
  pf↓ : ∀ {x : A} → (∀ {y : A} → x > y → ↓ _>_ y) → ↓ _>_ x

↓𝔹 : ∀ {ℓ}{A : Set ℓ} (_>_ : A → A → 𝔹) → A → Set ℓ 
↓𝔹{ℓ}{A} _>_ x = ↓{ℓ}{lzero} (λ (x y : A) → (x > y) ≡ tt) x

----------------------------------------------------------------------
-- theorems
----------------------------------------------------------------------

-----------------------------------
-- natural number > is terminating
-----------------------------------
↓-> : ∀ (x : ℕ) → ↓𝔹 _>_ x
↓-> x = pf↓ (h x)
  where h : ∀ x → ∀ {y} → x > y ≡ tt → ↓𝔹 _>_ y
        h 0 {0} () 
        h 0 {suc y} () 
        h (suc x) {y} p with <-drop {y} p 
        h (suc x) {y} p | inj₁ u rewrite u = ↓-> x
        h (suc x) {y} p | inj₂ u = h x u

{-
↓-> : ∀ (n : ℕ) → ↓𝔹 _>_ n
↓-> n = pf↓ (lem n)
  where lem : ∀ y → ∀ {x} → y > x ≡ tt → ↓𝔹 _>_ x
        lem 0 {0} () 
        lem 0 {suc y} () 
        lem (suc x) {y} p with <-drop {y} p 
        lem (suc x) {y} p | inj₁ u rewrite u = ↓-> x
        lem (suc x) {y} p | inj₂ u = lem x u
-}

------------------------------
-- lexicographic combination
------------------------------
module lexcomb {ℓ ℓ' ℓ1 ℓ2 : level}{A : Set ℓ}{B : Set ℓ'}(_>A_ : A → A → Set ℓ1)(_>B_ : B → B → Set ℓ2) where
  
  _>lex_ : A × B → A × B → Set (ℓ ⊔ ℓ1 ⊔ ℓ2)
  (a , b) >lex (a' , b') = a >A a' ∨ (a ≡ a' ∧ b >B b')

  {- If _>A_ is well-founded below a and if _>B_ is well-founded below every b, then
     _>lex_ is well-founded below (a , b) -}
  ↓-lex : {a : A} → ↓ _>A_ a → ((b : B) → ↓ _>B_ b) → {b : B} → ↓ _>lex_ (a , b)
  ↓-lex {a} (pf↓ fA) tB {b} = pf↓ (helper fA (tB b))
     where helper : {a : A} → (∀{y : A} → a >A y → ↓ _>A_ y) → {b : B} → ↓ _>B_ b → {y : A × B} → (a , b) >lex y → ↓ _>lex_ y
           helper fA _ {a' , b'} (inj₁ u) = ↓-lex (fA u) tB
           helper fA (pf↓ fB) {a' , b'} (inj₂ (u , u')) rewrite u = pf↓ (helper fA (fB u'))

------------------------------
-- measure functions
------------------------------

{- Suppose we want to prove that _>A_ is terminating starting from a, and we have a function m, 
   called a measure function, that maps A to another type B, where we know an 
   ordering _>B_ is terminating starting from (m a).

   Then as long as m is preserved by _>A_ -- meaning that a >A a' implies m a >B m a' -- then we
   can derive termination starting from a from termination starting from b. -}
module measure {ℓ ℓ' ℓ1 ℓ2 : level}{A : Set ℓ}{B : Set ℓ'}(_>A_ : A → A → Set ℓ1)(_>B_ : B → B → Set ℓ2)
               (m : A → B)
               (decreasem : ∀{a a' : A} → a >A a' → m a >B m a') where

  measure-↓ : ∀ {a : A} → ↓ _>B_ (m a) → ↓ _>A_ a
  measure-↓{a} (pf↓ fM) = pf↓ h
    where h : {y : A} → a >A y → ↓ _>A_ y
          h{y} p = measure-↓ (fM (decreasem p))

------------------------------
-- Newman's Lemma
------------------------------

{-
{- Newman's Lemma says that local confluence implies confluence for
   terminating elements of the relation (the usual formulation speaks
   about these properties for the whole relation, not just elements,
   but this is an obvious refinement). -}

module newman {ℓ ℓ' : level}{A : Set ℓ}(_>A_ : A → A → Set ℓ')
              (lc : ∀{a b c : A} → a >A b → a >A c → ∃ A (λ d → b >A d ∧ c >A d)) where

  open import relations _>A_ using (_tc_ ; tc-step ; tc-trans)

{-  In progress...

  the_lemma : ∀{a b c : A} → ↓ _>A_ a → a tc b → a tc c → ∃ A (λ d → b tc d ∧ c tc d)
  the_lemma w (tc-step u) (tc-step v) with lc u v 
  the_lemma w (tc-step u) (tc-step v) | d , u' , v' = d , tc-step u' , tc-step v'
  the_lemma w (tc-step u) (tc-trans v1 v2) = {!!}
  the_lemma w (tc-trans u1 u2) (tc-step v) = {!!}
  the_lemma w (tc-trans u1 u2) (tc-trans v1 v2) = {!!}
-}-}