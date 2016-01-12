module hnf where

open import lib

open import cedille-types
open import ctxt
open import is-free
open import rename
open import subst
open import syntax-util
open import to-string

{- Some notes:

   -- hnf{TERM} currently implements erasure as well as normalization.

   -- hnf{TYPE} does not descend into terms.
-}

{-# NO_TERMINATION_CHECK #-}
hnf : {ed : exprd} → ctxt → (unfold-rec : 𝔹) → ⟦ ed ⟧ → ⟦ ed ⟧
hnf{TERM} Γ u (Parens _ t _) = hnf Γ u t
hnf{TERM} Γ u (App t1 Erased t2) = hnf Γ u t1
hnf{TERM} Γ u (App t1 NotErased t2) with hnf Γ u t1
hnf{TERM} Γ u (App _ NotErased t2) | Lam _ _ _ x _ t1 = hnf Γ u (subst-term Γ t2 x t1)
hnf{TERM} Γ u (App _ NotErased t2) | t1 = App t1 NotErased (hnf Γ ff t2)
hnf{TERM} Γ u (Lam _ ErasedLambda _ _ _ t) = hnf Γ u t
hnf{TERM} Γ u (Lam pi KeptLambda pi' x oc t) = Lam pi KeptLambda pi' x NoClass (hnf (ctxt-var-decl x Γ) ff t)
hnf{TERM} Γ u (Var pi x) with ctxt-lookup-term-var-def Γ x
hnf{TERM} Γ u (Var pi x) | nothing = Var pi x
hnf{TERM} Γ u (Var pi x) | just t = t
hnf{TERM} Γ u (AppTp t tp) = hnf Γ u t

hnf{TYPE} Γ u (TpParens _ t _) = hnf Γ u t
hnf{TYPE} Γ u (TpVar _ x) with ctxt-lookup-type-var-def Γ x
hnf{TYPE} Γ ff (TpVar pi x) | nothing = TpVar pi x
hnf{TYPE} Γ tt (TpVar pi x) | nothing with ctxt-lookup-rec-def Γ x
hnf{TYPE} Γ tt (TpVar pi x) | nothing | nothing = TpVar pi x
hnf{TYPE} Γ tt (TpVar pi x) | nothing | just tp = tp
hnf{TYPE} Γ u (TpVar pi x) | just tp = tp
hnf{TYPE} Γ u (TpAppt tp t) with hnf Γ u tp
hnf{TYPE} Γ u (TpAppt _ t) | TpLambda _ _ x _ tp = hnf Γ u (subst-type Γ t x tp)
hnf{TYPE} Γ u (TpAppt _ t) | tp = TpAppt tp t
hnf{TYPE} Γ u (TpApp tp tp') with hnf Γ u tp
hnf{TYPE} Γ u (TpApp _ tp') | TpLambda _ _ x _ tp = hnf Γ u (subst-type Γ tp' x tp)
hnf{TYPE} Γ u (TpApp _ tp') | tp = TpApp tp (hnf Γ u tp')
hnf{TYPE} Γ u (Abs pi b pi' x atk tp) with to-abs (Abs pi b pi' x atk (hnf (ctxt-var-decl x Γ) u tp))
hnf{TYPE} Γ u (Abs _ _ _ _ _ _) | just (mk-abs pi b pi' x atk tt {- x is free in tp -} tp) = Abs pi b pi' x atk tp
hnf{TYPE} Γ u (Abs _ _ _ _ _ _) | just (mk-abs pi b pi' x (Tkk k) ff tp) = tp -- all kinds are inhabited, so it is safe to drop this
hnf{TYPE} Γ u (Abs _ _ _ _ _ _) | just (mk-abs pi All pi' x (Tkt tp') ff tp) = Abs pi All pi' x (Tkt tp') tp
hnf{TYPE} Γ u (Abs _ _ _ _ _ _) | just (mk-abs pi Pi pi' x (Tkt tp') ff tp) = TpArrow tp' tp
hnf{TYPE} Γ u (Abs pi b pi' x atk tp) | nothing = Abs pi b pi' x atk (hnf (ctxt-var-decl x Γ) u tp)
hnf{TYPE} Γ u (TpArrow tp1 tp2) = TpArrow (hnf Γ u tp1) (hnf Γ u tp2)

-- need to cover lifting cases still

hnf{KIND} Γ u (KndParens _ k _) = hnf Γ u k
hnf{KIND} Γ u (KndVar _ x) with ctxt-lookup-kind-var-def Γ x
hnf{KIND} Γ u (KndVar pi x) | nothing = KndVar pi x
hnf{KIND} Γ u (KndVar pi x) | just k = k
hnf{KIND} Γ u (KndPi pi pi' x atk k) =
  if is-free-in-kind check-erased x k then
    (KndPi pi pi' x atk k)
  else
    tk-arrow-kind atk k
hnf Γ u x = x

