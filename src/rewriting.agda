module rewriting where

open import lib

open import cedille-types
open import conversion
open import ctxt
open import is-free
open import rename
open import syntax-util

{- =ACG= =NOTE=
 - RewriteA labels a group of functions designed to pair something with a 
   natural number
 - RewriteA-pure pairs the input with 0
 - RewriteA-app is an infix operator which takes a rewrite function and 
   argument, applies the function to the argument and adds their nats together
 - Rewrite-return: when applied to some (a) and pair (rewriteA a'), will return 
   (rewriteA a) if the pair has zero as its nat, and (rewriteA a') otherwise.
 -}
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

{- we assume the term has already been put in hnf (erased would be ok except that we are retaining let-terms when we erase,
   but we are removing them when calling hnf). -}
{-# TERMINATING #-}
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
  else (rewrite-return t (rewrite-termh Γ ρ u t1 t2 (if u then (hnf Γ unfold-head t tt) else t)))

rewrite-term : rewrite-t term
rewrite-term Γ ρ u t1 t2 t = rewrite-terma Γ ρ u t1 t2 (erase-term t)

{-# TERMINATING #-}
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
rewrite-type Γ ρ u t1 t2 T | IotaEx pi ie pi' y m tp = 
  let y' = rename-var-if Γ ρ y (App t1 NotErased t2) in
    rewrite-return T
      ((rewriteA-pure (IotaEx pi ie pi' y)) rewriteA-app
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
{- =ACG= =NOTE=
 - We are attempting to rewrite TpArrow. Note:
   rewrite-type : 
     ctxt → renamectxt → (use-hnf : 𝔹) → term → term → Type → rewriteA Type
 - In this case, T = TpArrow tp _ tp'
 - rewriteA-app associates to the left, so the second rewriteA-app is higher in 
   the parse tree than the first
 - we have no rule for rewriting arrowtype, therefore, we will rewrite it using 
   rewriteA-pure
 -}
rewrite-type Γ ρ u t1 t2 T | TpArrow tp arrowtype tp' =
  rewrite-return T
    ((rewriteA-pure TpArrow) rewriteA-app
       (rewrite-type Γ ρ u t1 t2 tp) rewriteA-app
       (rewriteA-pure arrowtype) rewriteA-app
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
rewrite-type Γ ρ u t1 t2 _ | TpHole pi = TpHole pi , 0 --ACG

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
