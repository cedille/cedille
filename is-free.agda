module is-free where

open import lib

open import cedille-types
open import ctxt
open import syntax-util

is-free-e = 𝔹
check-erased = tt
skip-erased = ff

is-free-in-term : is-free-e → var → term → 𝔹
is-free-in-type : is-free-e → var → type → 𝔹
is-free-in-kind : is-free-e → var → kind → 𝔹
is-free-in-tk : is-free-e → var → tk → 𝔹
is-free-in-liftingType : is-free-e → var → liftingType → 𝔹

is-free-in-term ce x (App t Erased t') = is-free-in-term ce x t || (ce && is-free-in-term ce x t')
is-free-in-term ce x (App t NotErased t') = is-free-in-term ce x t || is-free-in-term ce x t'
is-free-in-term ce x (AppTp t tp) = is-free-in-term ce x t || (ce && is-free-in-type ce x tp)
is-free-in-term ce x (Hole x₁) = ff
is-free-in-term ce x (Lam _ b x' NoClass t) = ~ (x =string x') && is-free-in-term ce x t
is-free-in-term ce x (Lam _ b x' (SomeClass atk) t) = (ce && is-free-in-tk ce x atk) || (~ (x =string x') && is-free-in-term ce x t)
is-free-in-term ce x (Parens x₁ t x₂) = is-free-in-term ce x t
is-free-in-term ce x (Var _ x') = x =string x'

is-free-in-type ce x (Abs _ _ x' atk t) = is-free-in-tk ce x atk || (~ (x =string x') && is-free-in-type ce x t)
is-free-in-type ce x (Lft _ t l) = is-free-in-term ce x t || is-free-in-liftingType ce x l
is-free-in-type ce x (TpApp t t') = is-free-in-type ce x t || is-free-in-type ce x t'
is-free-in-type ce x (TpAppt t t') = is-free-in-type ce x t || is-free-in-term ce x t'
is-free-in-type ce x (TpArrow t t') = is-free-in-type ce x t || is-free-in-type ce x t'
is-free-in-type ce x (TpEq t t') = is-free-in-term ce x t || is-free-in-term ce x t'
is-free-in-type ce x (TpParens x₁ t x₂) = is-free-in-type ce x t
is-free-in-type ce x (TpVar _ x') = x =string x'

is-free-in-kind ce x (KndArrow k k') = is-free-in-kind ce x k || is-free-in-kind ce x k'
is-free-in-kind ce x (KndParens x₁ k x₂) = is-free-in-kind ce x k
is-free-in-kind ce x (KndPi _ x' atk k) = is-free-in-tk ce x atk || (~ (x =string x') && is-free-in-kind ce x k)
is-free-in-kind ce x (KndTpArrow t k) = is-free-in-type ce x t || is-free-in-kind ce x k
is-free-in-kind ce x (KndVar _ x') = x =string x'
is-free-in-kind ce x (Star x₁) = ff

is-free-in-tk ce x (Tkt t) = is-free-in-type ce x t
is-free-in-tk ce x (Tkk k) = is-free-in-kind ce x k

is-free-in-liftingType ce x (LiftArrow l l') = is-free-in-liftingType ce x l || is-free-in-liftingType ce x l'
is-free-in-liftingType ce x (LiftParens x₁ l x₂) = is-free-in-liftingType ce x l
is-free-in-liftingType ce x (LiftPi _ x' t l) = is-free-in-type ce x t || (~ (x =string x') && is-free-in-liftingType ce x l)
is-free-in-liftingType ce x (LiftStar x₁) = ff
is-free-in-liftingType ce x (LiftTpArrow t l) = is-free-in-type ce x t || is-free-in-liftingType ce x l
