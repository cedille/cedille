module hnf where

open import lib

open import cedille-types
open import ctxt
open import rename
open import subst
open import syntax-util

{-# NO_TERMINATION_CHECK #-}
hnf : {ed : exprd} → ctxt → ⟦ ed ⟧ → ⟦ ed ⟧
hnf{TERM} Γ (Parens _ t _) = hnf Γ t

hnf{TYPE} Γ (TpParens _ t _) = hnf Γ t
hnf{TYPE} Γ (TpVar _ x) with ctxt-lookup-type-var-def Γ x
hnf{TYPE} Γ (TpVar pi x) | nothing = TpVar pi x
hnf{TYPE} Γ (TpVar pi x) | just t = t
hnf{TYPE} Γ (TpAppt tp t) with hnf Γ tp
hnf{TYPE} Γ (TpAppt _ t) | Abs _ TpLambda x _ tp = hnf Γ (subst-type Γ t x tp)
hnf{TYPE} Γ (TpAppt _ t) | tp = TpAppt tp t
hnf{TYPE} Γ (TpApp tp tp') with hnf Γ tp
hnf{TYPE} Γ (TpApp _ tp') | Abs _ TpLambda x _ tp = hnf Γ (subst-type Γ tp' x tp)
hnf{TYPE} Γ (TpApp _ tp') | tp = TpApp tp tp'
-- need to cover lifting cases still

hnf{KIND} Γ (KndParens _ k _) = hnf Γ k
hnf{KIND} Γ (KndVar _ x) with ctxt-lookup-kind-var-def Γ x
hnf{KIND} Γ (KndVar pi x) | nothing = KndVar pi x
hnf{KIND} Γ (KndVar pi x) | just k = k
hnf Γ e = e
