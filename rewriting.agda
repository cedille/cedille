module rewriting where

open import lib

open import cedille-types
open import conversion
open import ctxt
open import is-free
open import rename
open import syntax-util

rewrite-t : Set → Set
rewrite-t T = ctxt → renamectxt → term → term → T → T

-- we assume the term is erased
rewrite-terma : rewrite-t term
rewrite-termh : rewrite-t term
rewrite-termh Γ ρ t1 t2 (App t x t') = App (rewrite-terma Γ ρ t1 t2 t) x (rewrite-terma Γ ρ t1 t2 t')
rewrite-termh Γ ρ t1 t2 (Beta x) = Beta x
rewrite-termh Γ ρ t1 t2 (Hole x) = Hole x
rewrite-termh Γ ρ t1 t2 (Lam pi KeptLambda pi' y NoClass t) =
  let y' = rename-var-if Γ ρ y (App t1 NotErased t2) in
    Lam pi KeptLambda pi' y' NoClass (rewrite-terma Γ (renamectxt-insert ρ y y') t1 t2 t)
rewrite-termh Γ ρ t1 t2 (Parens x t x₁) = rewrite-terma Γ ρ t1 t2 t
rewrite-termh Γ ρ t1 t2 (Var x x₁) = Var x (renamectxt-rep ρ x₁)
rewrite-termh Γ ρ t1 t2 x = x -- should not happen, as the term is erased

rewrite-terma Γ ρ t1 t2 t = 
  if conv-term Γ t1 t then t2
  else rewrite-termh Γ ρ t1 t2 t

rewrite-term : rewrite-t term
rewrite-term Γ ρ t1 t2 t = rewrite-terma Γ ρ t1 t2 (erase-term t)

rewrite-type : rewrite-t type
rewrite-kind : rewrite-t kind
rewrite-tk : rewrite-t tk
rewrite-optClass : rewrite-t optClass
rewrite-liftingType : rewrite-t liftingType

rewrite-type Γ ρ t1 t2 (Abs pi b pi' y tk tp) = 
  let y' = rename-var-if Γ ρ y (App t1 NotErased t2) in
    Abs pi b pi' y' (rewrite-tk Γ ρ t1 t2 tk) (rewrite-type Γ (renamectxt-insert ρ y y') t1 t2 tp)
rewrite-type Γ ρ t1 t2 (Iota pi y tp) = 
  let y' = rename-var-if Γ ρ y (App t1 NotErased t2) in
    Iota pi y (rewrite-type Γ (renamectxt-insert ρ y y') t1 t2 tp)
rewrite-type Γ ρ t1 t2 (Lft pi pi' y t l) = 
  let y' = rename-var-if Γ ρ y (App t1 NotErased t2) in
     Lft pi pi' y' (rewrite-term Γ (renamectxt-insert ρ y y') t1 t2 t) (rewrite-liftingType Γ ρ t1 t2 l)
rewrite-type Γ ρ t1 t2 (TpApp tp tp') = TpApp (rewrite-type Γ ρ t1 t2 tp) (rewrite-type Γ ρ t1 t2 tp')
rewrite-type Γ ρ t1 t2 (TpAppt tp t) = TpAppt (rewrite-type Γ ρ t1 t2 tp) (rewrite-term Γ ρ t1 t2 t)
rewrite-type Γ ρ t1 t2 (TpArrow tp tp') = TpArrow (rewrite-type Γ ρ t1 t2 tp) (rewrite-type Γ ρ t1 t2 tp')
rewrite-type Γ ρ t1 t2 (TpEq ta tb) = TpEq (rewrite-term Γ ρ t1 t2 ta) (rewrite-term Γ ρ t1 t2 tb)
rewrite-type Γ ρ t1 t2 (TpLambda pi pi' y atk t') = 
  let y' = rename-var-if Γ ρ y (App t1 NotErased t2) in
    TpLambda pi pi' y (rewrite-tk Γ ρ t1 t2 atk) (rewrite-type Γ (renamectxt-insert ρ y y') t1 t2 t')
rewrite-type Γ ρ t1 t2 (TpParens x tp x₁) = rewrite-type Γ ρ t1 t2 tp
rewrite-type Γ ρ t1 t2 (NoSpans tp _) = rewrite-type Γ ρ t1 t2 tp
rewrite-type Γ ρ t1 t2 (TpVar pi x) = TpVar pi (renamectxt-rep ρ x)

rewrite-kind Γ ρ t1 t2 k = k -- unimplemented

rewrite-tk Γ ρ t1 t2 (Tkt x) = Tkt (rewrite-type Γ ρ t1 t2 x)
rewrite-tk Γ ρ t1 t2 (Tkk x) = Tkk (rewrite-kind Γ ρ t1 t2 x)

rewrite-optClass Γ ρ t1 t2 NoClass = NoClass
rewrite-optClass Γ ρ t1 t2 (SomeClass x) = SomeClass (rewrite-tk Γ ρ t1 t2 x)

rewrite-liftingType Γ ρ t1 t2 l = l
