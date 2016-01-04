module subst where

open import lib

open import cedille-types
open import ctxt
open import is-free
open import rename
open import syntax-util

rename-var-if-in : {is-term : 𝔹} → ctxt → renamectxt → var → select-term-type is-term → var
rename-var-if-in Γ ρ x t = if is-free-in check-erased x t then (rename-away-from x (ctxt-binds-var Γ) ρ) else x

subst-ret-t : Set → Set
subst-ret-t T = {is-term : 𝔹} → ctxt → renamectxt → select-term-type is-term → var → T → T

subst-term : subst-ret-t term
subst-type : subst-ret-t type
subst-kind : subst-ret-t kind
subst-tk : subst-ret-t tk
subst-optClass : subst-ret-t optClass
subst-liftingType : subst-ret-t liftingType

subst-term Γ ρ t x (App t' m t'') = App (subst-term Γ ρ t x t') m (subst-term Γ ρ t x t'')
subst-term Γ ρ t x (AppTp t' tp) = AppTp (subst-term Γ ρ t x t') (subst-type Γ ρ t x tp)
subst-term Γ ρ t x (Hole x₁) = Hole x₁
subst-term Γ ρ t x (Lam pi b y oc t') = 
  let y' = rename-var-if-in Γ ρ y t in
    Lam pi b y' (subst-optClass Γ ρ t x oc) (subst-term Γ (renamectxt-insert ρ y y') t x t')
subst-term Γ ρ t x (Parens x₁ t' x₂) = subst-term Γ ρ t x t'
subst-term{tt} Γ ρ t x (Var pi y) =
 let y' = renamectxt-rep ρ y in
   if y' =string x then t else (Var pi y')
subst-term{ff} Γ ρ t x (Var pi y) = Var pi y
subst-type Γ ρ t x (Abs pi b y atk t') = 
  let y' = rename-var-if-in Γ ρ y t in
    Abs pi b y' (subst-tk Γ ρ t x atk) (subst-type Γ (renamectxt-insert ρ y y') t x t')
subst-type Γ ρ t x (Lft pi t' l) = Lft pi (subst-term Γ ρ t x t') (subst-liftingType Γ ρ t x l)
subst-type Γ ρ t x (TpApp tp tp₁) = TpApp (subst-type Γ ρ t x tp) (subst-type Γ ρ t x tp₁)
subst-type Γ ρ t x (TpAppt tp t') = TpAppt (subst-type Γ ρ t x tp) (subst-term Γ ρ t x t')
subst-type Γ ρ t x (TpArrow tp tp₁) = TpArrow (subst-type Γ ρ t x tp) (subst-type Γ ρ t x tp₁)
subst-type Γ ρ t x (TpEq x₁ x₂) = TpEq (subst-term Γ ρ t x x₁) (subst-term Γ ρ t x x₂)
subst-type Γ ρ t x (TpParens x₁ tp x₂) = subst-type Γ ρ t x tp
subst-type{tt} Γ ρ t x (TpVar pi y) = TpVar pi y
subst-type{ff} Γ ρ t x (TpVar pi y) =
 let y' = renamectxt-rep ρ y in
   if y' =string x then t else (TpVar pi y')
subst-kind Γ ρ t x (KndArrow k k₁) = KndArrow (subst-kind Γ ρ t x k) (subst-kind Γ ρ t x k₁)
subst-kind Γ ρ t x (KndParens x₁ k x₂) = subst-kind Γ ρ t x k
subst-kind Γ ρ t x (KndPi pi y atk k) = 
  let y' = rename-var-if-in Γ ρ y t in
    KndPi pi y' (subst-tk Γ ρ t x atk) (subst-kind Γ (renamectxt-insert ρ y y') t x k)
subst-kind Γ ρ t x (KndTpArrow t' k) = KndTpArrow (subst-type Γ ρ t x t') (subst-kind Γ ρ t x k)
subst-kind Γ ρ t x (KndVar pi y) = KndVar pi y
subst-kind Γ ρ t x (Star pi) = Star pi

subst-tk Γ ρ t x (Tkk k) = Tkk (subst-kind Γ ρ t x k)
subst-tk Γ ρ t x (Tkt t') = Tkt (subst-type Γ ρ t x t')

subst-optClass Γ ρ t x NoClass = NoClass
subst-optClass Γ ρ t x (SomeClass atk) = SomeClass (subst-tk Γ ρ t x atk)
subst-liftingType Γ ρ t x l = l -- unimplemented
