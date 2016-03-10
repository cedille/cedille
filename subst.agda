module subst where

open import lib

open import cedille-types
open import ctxt
open import is-free
open import rename
open import syntax-util

substh-ret-t : Set → Set
substh-ret-t T = {ed : exprd} → ctxt → renamectxt → ⟦ ed ⟧ → var → T → T

substh-term : substh-ret-t term
substh-type : substh-ret-t type
substh-kind : substh-ret-t kind
substh-tk : substh-ret-t tk
substh-optClass : substh-ret-t optClass
substh-liftingType : substh-ret-t liftingType
substh-maybeAtype : substh-ret-t maybeAtype

subst-rename-var-if : {ed : exprd} → ctxt → renamectxt → var → var → ⟦ ed ⟧ → var
subst-rename-var-if Γ ρ x y t = 
  {- rename bound variable y iff it is x (var being substituted for), or if y occurs free
     in t (the term we are substituting for x), or if it is the renamed version of any variable -}
  if x =string y || is-free-in check-erased y t || renamectxt-in-range ρ y then 
    rename-away-from y (λ s → ctxt-binds-var Γ s || s =string x) ρ
  else
    y


substh-term Γ ρ t x (App t' m t'') = App (substh-term Γ ρ t x t') m (substh-term Γ ρ t x t'')
substh-term Γ ρ t x (AppTp t' tp) = AppTp (substh-term Γ ρ t x t') (substh-type Γ ρ t x tp)
substh-term Γ ρ t x (Hole x₁) = Hole x₁
substh-term Γ ρ t x (Lam pi b pi' y oc t') =
  let y' = subst-rename-var-if Γ ρ x y t in
    Lam pi b pi' y' (substh-optClass Γ ρ t x oc) 
      (substh-term (ctxt-var-decl y' Γ) (renamectxt-insert ρ y y') t x t')
substh-term Γ ρ t x (Parens x₁ t' x₂) = substh-term Γ ρ t x t'
substh-term{TERM} Γ ρ t x (Var pi y) =
 let y' = renamectxt-rep ρ y in
   if y' =string x then t else (Var pi y')
substh-term Γ ρ t x (Var pi y) = Var pi (renamectxt-rep ρ y)
substh-term Γ ρ t x (Beta pi) = Beta pi
substh-term Γ ρ t x (Delta pi t') = Delta pi (substh-term Γ ρ t x t')
substh-term Γ ρ t x (PiInj pi n t') = PiInj pi n (substh-term Γ ρ t x t')
substh-term Γ ρ t x (Epsilon pi lr m t') = Epsilon pi lr m (substh-term Γ ρ t x t')
substh-term Γ ρ t x (Sigma pi t') = Sigma pi (substh-term Γ ρ t x t')
substh-term Γ ρ t x (Rho pi t' t'') = Rho pi (substh-term Γ ρ t x t') (substh-term Γ ρ t x t'')
substh-term Γ ρ t x (Chi pi T t'') = Chi pi (substh-maybeAtype Γ ρ t x T) (substh-term Γ ρ t x t'')
substh-term Γ ρ t x (Theta pi u t' ls) = Theta pi u (substh-term Γ ρ t x t') (substh-lterms Γ ρ t x ls) 
  where substh-lterms : substh-ret-t lterms
        substh-lterms Γ ρ t x (LtermsNil pi) = LtermsNil pi
        substh-lterms Γ ρ t x (LtermsCons t' ls) = LtermsCons (substh-term Γ ρ t x t') (substh-lterms Γ ρ t x ls)

substh-type Γ ρ t x (Abs pi b pi' y atk t') = 
  let y' = subst-rename-var-if Γ ρ x y t in
    Abs pi b pi' y' (substh-tk Γ ρ t x atk)
      (substh-type (ctxt-var-decl y' Γ) (renamectxt-insert ρ y y') t x t')
substh-type Γ ρ t x (TpLambda pi pi' y atk t') = 
  let y' = subst-rename-var-if Γ ρ x y t in
    TpLambda pi pi' y' (substh-tk Γ ρ t x atk) 
      (substh-type (ctxt-var-decl y' Γ) (renamectxt-insert ρ y y') t x t')
substh-type Γ ρ t x (Iota pi y m t') = 
  let y' = subst-rename-var-if Γ ρ x y t in
    Iota pi y' (substh-optClass Γ ρ t x m)
      (substh-type (ctxt-var-decl y' Γ) (renamectxt-insert ρ y y') t x t')
substh-type Γ ρ t x (Lft pi pi' y t' l) = 
  let y' = subst-rename-var-if Γ ρ x y t in
    Lft pi pi' y' (substh-term (ctxt-var-decl y' Γ) (renamectxt-insert ρ y y') t x t') 
      (substh-liftingType Γ ρ t x l)
substh-type Γ ρ t x (TpApp tp tp₁) = TpApp (substh-type Γ ρ t x tp) (substh-type Γ ρ t x tp₁)
substh-type Γ ρ t x (TpAppt tp t') = TpAppt (substh-type Γ ρ t x tp) (substh-term Γ ρ t x t')
substh-type Γ ρ t x (TpArrow tp tp₁) = TpArrow (substh-type Γ ρ t x tp) (substh-type Γ ρ t x tp₁)
substh-type Γ ρ t x (TpEq x₁ x₂) = TpEq (substh-term Γ ρ t x x₁) (substh-term Γ ρ t x x₂)
substh-type Γ ρ t x (TpParens x₁ tp x₂) = substh-type Γ ρ t x tp
substh-type Γ ρ t x (NoSpans tp _) = substh-type Γ ρ t x tp
substh-type{TYPE} Γ ρ t x (TpVar pi y) =
 let y' = renamectxt-rep ρ y in
   if y' =string x then t else (TpVar pi y')
substh-type Γ ρ t x (TpVar pi y) = TpVar pi (renamectxt-rep ρ y)
substh-kind Γ ρ t x (KndArrow k k₁) = KndArrow (substh-kind Γ ρ t x k) (substh-kind Γ ρ t x k₁)
substh-kind Γ ρ t x (KndParens x₁ k x₂) = substh-kind Γ ρ t x k
substh-kind Γ ρ t x (KndPi pi pi' y atk k) = 
  let y' = subst-rename-var-if Γ ρ x y t in
    KndPi pi pi' y' (substh-tk Γ ρ t x atk)
      (substh-kind (ctxt-var-decl y' Γ) (renamectxt-insert ρ y y') t x k)
substh-kind Γ ρ t x (KndTpArrow t' k) = KndTpArrow (substh-type Γ ρ t x t') (substh-kind Γ ρ t x k)
substh-kind Γ ρ t x (KndVar pi y) = KndVar pi y
substh-kind Γ ρ t x (Star pi) = Star pi

substh-tk Γ ρ t x (Tkk k) = Tkk (substh-kind Γ ρ t x k)
substh-tk Γ ρ t x (Tkt t') = Tkt (substh-type Γ ρ t x t')

substh-optClass Γ ρ t x NoClass = NoClass
substh-optClass Γ ρ t x (SomeClass atk) = SomeClass (substh-tk Γ ρ t x atk)
substh-liftingType Γ ρ t x l = l -- unimplemented

substh-maybeAtype Γ ρ t x NoAtype = NoAtype
substh-maybeAtype Γ ρ t x (Atype T) = Atype (substh-type Γ ρ t x T)

subst-ret-t : Set → Set
subst-ret-t T = {ed : exprd} → ctxt → ⟦ ed ⟧ → var → T → T

subst-term : subst-ret-t term
subst-term Γ t x a = substh-term Γ empty-renamectxt t x a

subst-type : subst-ret-t type
subst-type Γ t x a = substh-type Γ empty-renamectxt t x a

subst-kind : subst-ret-t kind
subst-kind Γ t x a = substh-kind Γ empty-renamectxt t x a

rename-type : ctxt → var → var → (is-term-var : 𝔹) → type → type
rename-type Γ x y tt tp = subst-type Γ (Var posinfo-gen y) x tp
rename-type Γ x y ff tp = subst-type Γ (TpVar posinfo-gen y) x tp

rename-kind : ctxt → var → var → (is-term-var : 𝔹) → kind → kind
rename-kind Γ x y tt k = subst-kind Γ (Var posinfo-gen y) x k
rename-kind Γ x y ff k = subst-kind Γ (TpVar posinfo-gen y) x k
