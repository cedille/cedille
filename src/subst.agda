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
substh-optType : substh-ret-t optType
substh-optTerm : substh-ret-t optTerm
substh-liftingType : substh-ret-t liftingType
substh-maybeAtype : substh-ret-t maybeAtype
substh-args : substh-ret-t args

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
      (substh-term (ctxt-var-decl posinfo-gen y' Γ) (renamectxt-insert ρ y y') t x t')
substh-term Γ ρ t x (Parens x₁ t' x₂) = substh-term Γ ρ t x t'
substh-term{TERM} Γ ρ t x (Var pi y) =
 let y' = renamectxt-rep ρ y in
   if y' =string x then t else (Var pi y')
substh-term Γ ρ t x (Var pi y) = Var pi (renamectxt-rep ρ y)
substh-term Γ ρ t x (Unfold pi t') = Unfold pi (substh-term Γ ρ t x t')
substh-term Γ ρ t x (Beta pi ot) = Beta pi (substh-optTerm Γ ρ t x ot)
substh-term Γ ρ t x (Delta pi t') = Delta pi (substh-term Γ ρ t x t')
substh-term Γ ρ t x (Omega pi t') = Omega pi (substh-term Γ ρ t x t')
substh-term Γ ρ t x (InlineDef pi pi' x' t' pi'') = InlineDef pi pi' x' (substh-term Γ ρ t x t') pi''
substh-term Γ ρ t x (IotaPair pi t1 t2 ot pi') = IotaPair pi (substh-term Γ ρ t x t1) (substh-term Γ ρ t x t2) (substh-optTerm Γ ρ t x ot) pi'
substh-term Γ ρ t x (IotaProj t' n pi) = IotaProj (substh-term Γ ρ t x t') n pi
substh-term Γ ρ t x (PiInj pi n t') = PiInj pi n (substh-term Γ ρ t x t')
substh-term Γ ρ t x (Epsilon pi lr m t') = Epsilon pi lr m (substh-term Γ ρ t x t')
substh-term Γ ρ t x (Sigma pi t') = Sigma pi (substh-term Γ ρ t x t')
substh-term Γ ρ t x (Rho pi r t' t'') = Rho pi r (substh-term Γ ρ t x t') (substh-term Γ ρ t x t'')
substh-term Γ ρ t x (Chi pi T t'') = Chi pi (substh-maybeAtype Γ ρ t x T) (substh-term Γ ρ t x t'')
substh-term Γ ρ t x (Theta pi u t' ls) = Theta pi u (substh-term Γ ρ t x t') (substh-lterms Γ ρ t x ls) 
  where substh-lterms : substh-ret-t lterms
        substh-lterms Γ ρ t x (LtermsNil pi) = LtermsNil pi
        substh-lterms Γ ρ t x (LtermsCons m t' ls) = LtermsCons m (substh-term Γ ρ t x t') (substh-lterms Γ ρ t x ls)

substh-type Γ ρ t x (Abs pi b pi' y atk t') = 
  let y' = subst-rename-var-if Γ ρ x y t in
    Abs pi b pi' y' (substh-tk Γ ρ t x atk)
      (substh-type (ctxt-var-decl posinfo-gen y' Γ) (renamectxt-insert ρ y y') t x t')
substh-type Γ ρ t x (Mu pi pi' y k t') =
  let y' = subst-rename-var-if Γ ρ x y t in
    Mu pi pi' y' (substh-kind Γ ρ t x k) 
      (substh-type (ctxt-var-decl posinfo-gen y' Γ) (renamectxt-insert ρ y y') t x t')
substh-type Γ ρ t x (TpLambda pi pi' y atk t') = 
  let y' = subst-rename-var-if Γ ρ x y t in
    TpLambda pi pi' y' (substh-tk Γ ρ t x atk) 
      (substh-type (ctxt-var-decl posinfo-gen y' Γ) (renamectxt-insert ρ y y') t x t')
substh-type Γ ρ t x (IotaEx pi ie pi' y m t') = 
  let y' = subst-rename-var-if Γ ρ x y t in
    IotaEx pi ie pi' y' (substh-optType Γ ρ t x m)
      (substh-type (ctxt-var-decl posinfo-gen y' Γ) (renamectxt-insert ρ y y') t x t')
substh-type Γ ρ t x (Lft pi pi' y t' l) = 
  let y' = subst-rename-var-if Γ ρ x y t in
    Lft pi pi' y' (substh-term (ctxt-var-decl posinfo-gen y' Γ) (renamectxt-insert ρ y y') t x t') 
      (substh-liftingType Γ ρ t x l)
substh-type Γ ρ t x (TpApp tp tp₁) = TpApp (substh-type Γ ρ t x tp) (substh-type Γ ρ t x tp₁)
substh-type Γ ρ t x (TpAppt tp t') = TpAppt (substh-type Γ ρ t x tp) (substh-term Γ ρ t x t')
substh-type Γ ρ t x (TpArrow tp arrowtype tp₁) = TpArrow (substh-type Γ ρ t x tp) arrowtype (substh-type Γ ρ t x tp₁)
substh-type Γ ρ t x (TpEq x₁ x₂) = TpEq (substh-term Γ ρ t x x₁) (substh-term Γ ρ t x x₂)
substh-type Γ ρ t x (TpParens x₁ tp x₂) = substh-type Γ ρ t x tp
substh-type Γ ρ t x (NoSpans tp _) = substh-type Γ ρ t x tp
substh-type{TYPE} Γ ρ t x (TpVar pi y) =
 let y' = renamectxt-rep ρ y in
   if y' =string x then t else (TpVar pi y')
substh-type Γ ρ t x (TpVar pi y) = TpVar pi (renamectxt-rep ρ y)
substh-type Γ ρ t x (TpHole pi) = TpHole pi --ACG
substh-kind Γ ρ t x (KndArrow k k₁) = KndArrow (substh-kind Γ ρ t x k) (substh-kind Γ ρ t x k₁)
substh-kind Γ ρ t x (KndParens x₁ k x₂) = substh-kind Γ ρ t x k
substh-kind Γ ρ t x (KndPi pi pi' y atk k) = 
  let y' = subst-rename-var-if Γ ρ x y t in
    KndPi pi pi' y' (substh-tk Γ ρ t x atk)
      (substh-kind (ctxt-var-decl posinfo-gen y' Γ) (renamectxt-insert ρ y y') t x k)
substh-kind Γ ρ t x (KndTpArrow t' k) = KndTpArrow (substh-type Γ ρ t x t') (substh-kind Γ ρ t x k)
substh-kind Γ ρ t x (KndVar pi y ys) = KndVar pi y (substh-args Γ ρ t x ys)
substh-kind Γ ρ t x (Star pi) = Star pi

substh-args Γ ρ t x (ArgsCons (TermArg x₁) ys) = ArgsCons (TermArg (substh-term Γ ρ t x x₁)) (substh-args Γ ρ t x ys)
substh-args Γ ρ t x (ArgsCons (TypeArg x₁) ys) = ArgsCons (TypeArg (substh-type Γ ρ t x x₁)) (substh-args Γ ρ t x ys)
substh-args Γ ρ t x (ArgsNil x₁) = ArgsNil x₁

substh-tk Γ ρ t x (Tkk k) = Tkk (substh-kind Γ ρ t x k)
substh-tk Γ ρ t x (Tkt t') = Tkt (substh-type Γ ρ t x t')

substh-optClass Γ ρ t x NoClass = NoClass
substh-optClass Γ ρ t x (SomeClass atk) = SomeClass (substh-tk Γ ρ t x atk)
substh-optType Γ ρ t x NoType = NoType
substh-optType Γ ρ t x (SomeType t1) = SomeType (substh-type Γ ρ t x t1)
substh-liftingType Γ ρ t x (LiftArrow l l₁) = LiftArrow (substh-liftingType Γ ρ t x l) (substh-liftingType Γ ρ t x l₁)
substh-liftingType Γ ρ t x (LiftParens x₁ l x₂) = substh-liftingType Γ ρ t x l
substh-liftingType Γ ρ t x (LiftPi pi y tp l) = 
  let y' = subst-rename-var-if Γ ρ x y t in 
    LiftPi pi y' (substh-type Γ ρ t x tp) 
       (substh-liftingType (ctxt-var-decl posinfo-gen y' Γ) (renamectxt-insert ρ y y') t x l)
substh-liftingType Γ ρ t x (LiftStar pi) = LiftStar pi
substh-liftingType Γ ρ t x (LiftTpArrow tp l) = 
  LiftTpArrow (substh-type Γ ρ t x tp) (substh-liftingType Γ ρ t x l)

substh-maybeAtype Γ ρ t x NoAtype = NoAtype
substh-maybeAtype Γ ρ t x (Atype T) = Atype (substh-type Γ ρ t x T)

substh-optTerm Γ ρ t x NoTerm = NoTerm
substh-optTerm Γ ρ t x (SomeTerm t' pi') = (SomeTerm (substh-term Γ ρ t x t') pi')

subst-ret-t : Set → Set
subst-ret-t T = {ed : exprd} → ctxt → ⟦ ed ⟧ → var → T → T

subst-term : subst-ret-t term
subst-term Γ t x a = substh-term Γ empty-renamectxt t x a

subst-type : subst-ret-t type
subst-type Γ t x a = substh-type Γ empty-renamectxt t x a

subst-kind : subst-ret-t kind
subst-kind Γ t x a = substh-kind Γ empty-renamectxt t x a

subst-liftingType : subst-ret-t liftingType
subst-liftingType Γ t x a = substh-liftingType Γ empty-renamectxt t x a

rename-type : ctxt → var → var → (is-term-var : 𝔹) → type → type
rename-type Γ x y tt tp = subst-type Γ (Var posinfo-gen y) x tp
rename-type Γ x y ff tp = subst-type Γ (TpVar posinfo-gen y) x tp

rename-kind : ctxt → var → var → (is-term-var : 𝔹) → kind → kind
rename-kind Γ x y tt k = subst-kind Γ (Var posinfo-gen y) x k
rename-kind Γ x y ff k = subst-kind Γ (TpVar posinfo-gen y) x k

unfold-mu : ctxt → type → type
unfold-mu Γ (Mu pi pi' x k body) = subst-type Γ (Mu pi pi' x k body) x body
unfold-mu Γ tp = tp
