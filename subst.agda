module subst where

open import lib

open import cedille-types
open import ctxt
open import is-free
open import rename
open import syntax-util

rename-var-if-in : {is-term : 𝔹} → ctxt → renamectxt → var → select-term-type is-term → var
rename-var-if-in Γ ρ x t = if is-free-in check-erased x t then (rename-away-from x (ctxt-binds-var Γ) ρ) else x

substh-ret-t : Set → Set
substh-ret-t T = {is-term : 𝔹} → ctxt → renamectxt → select-term-type is-term → var → T → T

substh-term : substh-ret-t term
substh-type : substh-ret-t type
substh-kind : substh-ret-t kind
substh-tk : substh-ret-t tk
substh-optClass : substh-ret-t optClass
substh-liftingType : substh-ret-t liftingType

substh-term Γ ρ t x (App t' m t'') = App (substh-term Γ ρ t x t') m (substh-term Γ ρ t x t'')
substh-term Γ ρ t x (AppTp t' tp) = AppTp (substh-term Γ ρ t x t') (substh-type Γ ρ t x tp)
substh-term Γ ρ t x (Hole x₁) = Hole x₁
substh-term Γ ρ t x (Lam pi b y oc t') = 
  let y' = rename-var-if-in Γ ρ y t in
    Lam pi b y' (substh-optClass Γ ρ t x oc) (substh-term Γ (renamectxt-insert ρ y y') t x t')
substh-term Γ ρ t x (Parens x₁ t' x₂) = substh-term Γ ρ t x t'
substh-term{tt} Γ ρ t x (Var pi y) =
 let y' = renamectxt-rep ρ y in
   if y' =string x then t else (Var pi y')
substh-term{ff} Γ ρ t x (Var pi y) = Var pi y
substh-type Γ ρ t x (Abs pi b y atk t') = 
  let y' = rename-var-if-in Γ ρ y t in
    Abs pi b y' (substh-tk Γ ρ t x atk) (substh-type Γ (renamectxt-insert ρ y y') t x t')
substh-type Γ ρ t x (Lft pi t' l) = Lft pi (substh-term Γ ρ t x t') (substh-liftingType Γ ρ t x l)
substh-type Γ ρ t x (TpApp tp tp₁) = TpApp (substh-type Γ ρ t x tp) (substh-type Γ ρ t x tp₁)
substh-type Γ ρ t x (TpAppt tp t') = TpAppt (substh-type Γ ρ t x tp) (substh-term Γ ρ t x t')
substh-type Γ ρ t x (TpArrow tp tp₁) = TpArrow (substh-type Γ ρ t x tp) (substh-type Γ ρ t x tp₁)
substh-type Γ ρ t x (TpEq x₁ x₂) = TpEq (substh-term Γ ρ t x x₁) (substh-term Γ ρ t x x₂)
substh-type Γ ρ t x (TpParens x₁ tp x₂) = substh-type Γ ρ t x tp
substh-type{tt} Γ ρ t x (TpVar pi y) = TpVar pi y
substh-type{ff} Γ ρ t x (TpVar pi y) =
 let y' = renamectxt-rep ρ y in
   if y' =string x then t else (TpVar pi y')
substh-kind Γ ρ t x (KndArrow k k₁) = KndArrow (substh-kind Γ ρ t x k) (substh-kind Γ ρ t x k₁)
substh-kind Γ ρ t x (KndParens x₁ k x₂) = substh-kind Γ ρ t x k
substh-kind Γ ρ t x (KndPi pi y atk k) = 
  let y' = rename-var-if-in Γ ρ y t in
    KndPi pi y' (substh-tk Γ ρ t x atk) (substh-kind Γ (renamectxt-insert ρ y y') t x k)
substh-kind Γ ρ t x (KndTpArrow t' k) = KndTpArrow (substh-type Γ ρ t x t') (substh-kind Γ ρ t x k)
substh-kind Γ ρ t x (KndVar pi y) = KndVar pi y
substh-kind Γ ρ t x (Star pi) = Star pi

substh-tk Γ ρ t x (Tkk k) = Tkk (substh-kind Γ ρ t x k)
substh-tk Γ ρ t x (Tkt t') = Tkt (substh-type Γ ρ t x t')

substh-optClass Γ ρ t x NoClass = NoClass
substh-optClass Γ ρ t x (SomeClass atk) = SomeClass (substh-tk Γ ρ t x atk)
substh-liftingType Γ ρ t x l = l -- unimplemented

subst-ret-t : Set → Set
subst-ret-t T = {is-term : 𝔹} → ctxt → select-term-type is-term → var → T → T

subst-term : subst-ret-t term
subst-term Γ t x a = substh-term Γ empty-renamectxt t x a

subst-type : subst-ret-t type
subst-type Γ t x a = substh-type Γ empty-renamectxt t x a

subst-kind : subst-ret-t kind
subst-kind Γ t x a = substh-kind Γ empty-renamectxt t x a

