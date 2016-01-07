module hnf where

open import lib

open import cedille-types
open import ctxt
open import rename
open import subst
open import syntax-util

whnf-term : ctxt → term → term
whnf-term Γ (Parens _ t _) = whnf-term Γ t
whnf-term Γ t = t

{-# NO_TERMINATION_CHECK #-}
whnf-type : ctxt → type → type
whnf-type Γ (TpParens _ t _) = whnf-type Γ t
whnf-type Γ (TpVar _ x) with ctxt-lookup-type-var-def Γ x
whnf-type Γ (TpVar pi x) | nothing = TpVar pi x
whnf-type Γ (TpVar pi x) | just t = t
whnf-type Γ (TpAppt tp t) with whnf-type Γ tp
whnf-type Γ (TpAppt _ t) | Abs _ TpLambda x _ tp = whnf-type Γ (subst-type Γ t x tp)
whnf-type Γ (TpAppt _ t) | tp = TpAppt tp t
whnf-type Γ (TpApp tp tp') with whnf-type Γ tp
whnf-type Γ (TpApp _ tp') | Abs _ TpLambda x _ tp = whnf-type Γ (subst-type Γ tp' x tp)
whnf-type Γ (TpApp _ tp') | tp = TpApp tp tp'
-- need to cover lifting cases still
whnf-type Γ t = t

whnf-kind : ctxt → kind → kind
whnf-kind Γ (KndParens _ k _) = whnf-kind Γ k
whnf-kind Γ (KndVar _ x) with ctxt-lookup-kind-var-def Γ x
whnf-kind Γ (KndVar pi x) | nothing = KndVar pi x
whnf-kind Γ (KndVar pi x) | just k = k
whnf-kind Γ k = k
