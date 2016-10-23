module rewriting where

open import lib

open import cedille-types
open import conversion
open import ctxt
open import is-free
open import rename
open import syntax-util

rewriteA : Set → Set
rewriteA T = T × ℕ

rewriteA-pure : ∀{A : Set} → A → rewriteA A
rewriteA-pure a = a , 0

infixl 4 _rewriteA-app_

_rewriteA-app_ : ∀{A B : Set} → rewriteA (A → B) → rewriteA A → rewriteA B
(f , x) rewriteA-app (a , y) = (f a , x + y)

rewrite-return : ∀{A : Set} → A → rewriteA A → rewriteA A
rewrite-return a (a' , 0) = a , 0
rewrite-return _ r = r

rewrite-t : Set → Set
rewrite-t T = ctxt → renamectxt → (use-hnf : 𝔹) → term → term → T → rewriteA T

-- we assume the term is erased
{-# NO_TERMINATION_CHECK #-}
rewrite-terma : rewrite-t term
rewrite-termh : rewrite-t term
rewrite-termh Γ ρ u t1 t2 orig with orig
rewrite-termh Γ ρ u t1 t2 orig | App t x t' =
  rewrite-return orig
    ((rewriteA-pure App) rewriteA-app
       (rewrite-terma Γ ρ u t1 t2 t) rewriteA-app
       (rewriteA-pure x) rewriteA-app
       (rewrite-terma Γ ρ u t1 t2 t'))
rewrite-termh Γ ρ u t1 t2 orig | Lam pi KeptLambda pi' y NoClass t =
  let y' = rename-var-if Γ ρ y (App t1 NotErased t2) in
    rewrite-return orig
      ((rewriteA-pure (Lam pi KeptLambda pi' y' NoClass)) rewriteA-app
         (rewrite-terma Γ (renamectxt-insert ρ y y') u t1 t2 t))
rewrite-termh Γ ρ u t1 t2 _ | Parens _ t _ = rewrite-terma Γ ρ u t1 t2 t
rewrite-termh Γ ρ u t1 t2 _ | Var x x₁ = Var x (renamectxt-rep ρ x₁) , 0
rewrite-termh Γ ρ u t1 t2 _ | x = x , 0

rewrite-terma Γ ρ u t1 t2 t = 
  if conv-term Γ t1 t then (t2 , 1)
  else (rewrite-return t (rewrite-termh Γ ρ u t1 t2 (if u then (hnf Γ unfold-head t) else t)))

rewrite-term : rewrite-t term
rewrite-term Γ ρ u t1 t2 t = rewrite-terma Γ ρ u t1 t2 (erase-term t)

{-# NO_TERMINATION_CHECK #-}
rewrite-type : rewrite-t type
rewrite-kind : rewrite-t kind
rewrite-tk : rewrite-t tk
rewrite-optClass : rewrite-t optClass
rewrite-optType : rewrite-t optType
rewrite-liftingType : rewrite-t liftingType

rewrite-type Γ ρ u t1 t2 T with T
rewrite-type Γ ρ u t1 t2 T | Abs pi b pi' y tk tp = 
  let y' = rename-var-if Γ ρ y (App t1 NotErased t2) in
    rewrite-return T
      ((rewriteA-pure (Abs pi b pi' y')) rewriteA-app
        (rewrite-tk Γ ρ u t1 t2 tk) rewriteA-app
        (rewrite-type Γ (renamectxt-insert ρ y y') u t1 t2 tp))
rewrite-type Γ ρ u t1 t2 T | Mu pi pi' y k tp = 
  let y' = rename-var-if Γ ρ y (App t1 NotErased t2) in
    rewrite-return T
      ((rewriteA-pure (Mu pi pi' y')) rewriteA-app
        (rewrite-kind Γ ρ u t1 t2 k) rewriteA-app
        (rewrite-type Γ (renamectxt-insert ρ y y') u t1 t2 tp))
rewrite-type Γ ρ u t1 t2 T | Iota pi pi' y m tp = 
  let y' = rename-var-if Γ ρ y (App t1 NotErased t2) in
    rewrite-return T
      ((rewriteA-pure (Iota pi pi' y)) rewriteA-app
         (rewrite-optType Γ ρ u t1 t2 m) rewriteA-app
         (rewrite-type Γ (renamectxt-insert ρ y y') u t1 t2 tp))
rewrite-type Γ ρ u t1 t2 T | Lft pi pi' y t l = 
  let y' = rename-var-if Γ ρ y (App t1 NotErased t2) in
     rewrite-return T
       ((rewriteA-pure (Lft pi pi' y')) rewriteA-app
          (rewrite-term Γ (renamectxt-insert ρ y y') u t1 t2 t) rewriteA-app
          (rewrite-liftingType Γ ρ u t1 t2 l))
rewrite-type Γ ρ u t1 t2 T | TpApp tp tp' =
  rewrite-return T
    ((rewriteA-pure TpApp) rewriteA-app
       (rewrite-type Γ ρ u t1 t2 tp) rewriteA-app
       (rewrite-type Γ ρ u t1 t2 tp'))
rewrite-type Γ ρ u t1 t2 T | TpAppt tp t =
  rewrite-return T
    ((rewriteA-pure TpAppt) rewriteA-app
       (rewrite-type Γ ρ u t1 t2 tp) rewriteA-app
       (rewrite-term Γ ρ u t1 t2 t))
rewrite-type Γ ρ u t1 t2 T | TpArrow tp tp' =
  rewrite-return T
    ((rewriteA-pure TpArrow) rewriteA-app
       (rewrite-type Γ ρ u t1 t2 tp) rewriteA-app
       (rewrite-type Γ ρ u t1 t2 tp'))
rewrite-type Γ ρ u t1 t2 T | TpEq ta tb =
  rewrite-return T
    ((rewriteA-pure TpEq) rewriteA-app
       (rewrite-term Γ ρ u t1 t2 ta) rewriteA-app
       (rewrite-term Γ ρ u t1 t2 tb))
rewrite-type Γ ρ u t1 t2 T | TpLambda pi pi' y atk t' = 
  let y' = rename-var-if Γ ρ y (App t1 NotErased t2) in
    rewrite-return T
      ((rewriteA-pure (TpLambda pi pi' y)) rewriteA-app
         (rewrite-tk Γ ρ u t1 t2 atk) rewriteA-app
         (rewrite-type Γ (renamectxt-insert ρ y y') u t1 t2 t'))
rewrite-type Γ ρ u t1 t2 _ | TpParens x tp x₁ = rewrite-type Γ ρ u t1 t2 tp
rewrite-type Γ ρ u t1 t2 _ | NoSpans tp _ = rewrite-type Γ ρ u t1 t2 tp
rewrite-type Γ ρ u t1 t2 _ | TpVar pi x = TpVar pi (renamectxt-rep ρ x) , 0

rewrite-kind Γ ρ u t1 t2 k = k , 0 -- unimplemented

rewrite-tk Γ ρ u t1 t2 (Tkt x) = rewrite-return (Tkt x)
                                  ((rewriteA-pure Tkt) rewriteA-app (rewrite-type Γ ρ u t1 t2 x))
rewrite-tk Γ ρ u t1 t2 (Tkk x) = rewrite-return (Tkk x)
                                  ((rewriteA-pure Tkk) rewriteA-app (rewrite-kind Γ ρ u t1 t2 x))

rewrite-optClass Γ ρ u t1 t2 NoClass = NoClass , 0
rewrite-optClass Γ ρ u t1 t2 (SomeClass x) = rewrite-return (SomeClass x)
                                              ((rewriteA-pure SomeClass) rewriteA-app (rewrite-tk Γ ρ u t1 t2 x))
rewrite-optType Γ ρ u t1 t2 NoType = NoType , 0
rewrite-optType Γ ρ u t1 t2 (SomeType x) = rewrite-return (SomeType x)
                                              ((rewriteA-pure SomeType) rewriteA-app (rewrite-type Γ ρ u t1 t2 x))

rewrite-liftingType Γ ρ u t1 t2 l = l , 0 -- unimplemented
