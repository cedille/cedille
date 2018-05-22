module is-free where

open import lib

open import cedille-types
open import ctxt-types
open import syntax-util
open import general-util

are-free-e = 𝔹
check-erased = tt
skip-erased = ff

are-free-in-t : Set → Set₁
are-free-in-t T = ∀{A} → are-free-e → trie A → T → 𝔹

are-free-in-term : are-free-in-t term
are-free-in-type : are-free-in-t type
are-free-in-kind : are-free-in-t kind
are-free-in-optClass : are-free-in-t optClass
-- are-free-in-optType : are-free-in-t optType
are-free-in-optTerm : are-free-in-t optTerm
are-free-in-optGuide : are-free-in-t optGuide
are-free-in-tk : are-free-in-t tk 
are-free-in-liftingType : are-free-in-t liftingType
are-free-in-maybeAtype : are-free-in-t maybeAtype
are-free-in-maybeCheckType : are-free-in-t maybeCheckType
are-free-in-args : are-free-in-t args

are-free-in-term ce x (App t Erased t') = are-free-in-term ce x t || (ce && are-free-in-term ce x t')
are-free-in-term ce x (App t NotErased t') = are-free-in-term ce x t || are-free-in-term ce x t'
are-free-in-term ce x (AppTp t tp) = are-free-in-term ce x t || (ce && are-free-in-type ce x tp)
are-free-in-term ce x (Hole x₁) = ff
are-free-in-term ce x (Lam _ b _ x' oc t) =
  (ce && are-free-in-optClass ce x oc)
  || are-free-in-term ce (trie-remove x x') t
are-free-in-term ce x (Let _ (DefTerm _ x' m t) t') =
  (ce && are-free-in-maybeCheckType ce x m) || (are-free-in-term ce x t)
  || are-free-in-term ce (trie-remove x x') t'
are-free-in-term ce x (Let _ (DefType _ x' k t) t') =
  (ce && (are-free-in-kind ce x k || are-free-in-type ce x t))
  || are-free-in-term ce (trie-remove x x') t'
are-free-in-term ce x (Parens x₁ t x₂) = are-free-in-term ce x t
are-free-in-term ce x (Var _ "_") = ff
are-free-in-term ce x (Var _ x') = trie-contains x x'
are-free-in-term ce x (Beta _ ot ot') = are-free-in-optTerm ce x ot' || (ce && are-free-in-optTerm ce x ot)
are-free-in-term ce x (IotaPair _ t1 t2 ot _) = are-free-in-term ce x t1 || (ce && (are-free-in-term ce x t2 || are-free-in-optGuide ce x ot))
are-free-in-term ce x (IotaProj t n _) = are-free-in-term ce x t
are-free-in-term ce x (Epsilon _ _ _ t) = are-free-in-term ce x t
are-free-in-term ce x (Sigma _ t) = are-free-in-term ce x t
are-free-in-term ce x (Phi _ t t₁ t₂ _) = (ce && are-free-in-term ce x t) || (ce && are-free-in-term ce x t₁) || are-free-in-term ce x t₂
are-free-in-term ce x (Rho _ _ _ t ot t') = (ce && (are-free-in-term ce x t || are-free-in-optGuide ce x ot)) || are-free-in-term ce x t'
are-free-in-term ce x (Chi _ T t') = (ce && are-free-in-maybeAtype ce x T) || are-free-in-term ce x t'
are-free-in-term ce x (Delta _ T t') = (ce && are-free-in-maybeAtype ce x T) || are-free-in-term ce x t'
are-free-in-term ce x (Theta _ _ t ls) = are-free-in-term ce x t || are-free-in-lterms ce x ls
  where are-free-in-lterms : ∀{A} → are-free-e → trie A → lterms → 𝔹
        are-free-in-lterms ce x (LtermsNil _) = ff
        are-free-in-lterms ce x (LtermsCons Erased t ls) = (ce && are-free-in-term ce x t) || are-free-in-lterms ce x ls
        are-free-in-lterms ce x (LtermsCons NotErased t ls) = are-free-in-term ce x t || are-free-in-lterms ce x ls

are-free-in-type ce x (Abs _ _ _ x' atk t) = are-free-in-tk ce x atk || are-free-in-type ce (trie-remove x x') t
are-free-in-type ce x (TpLambda _ _ x' atk t) = are-free-in-tk ce x atk || are-free-in-type ce (trie-remove x x') t
are-free-in-type ce x (Iota _ _ x' m t) = are-free-in-type ce x m || are-free-in-type ce (trie-remove x x') t
are-free-in-type ce x (Lft _ _ X t l) = are-free-in-liftingType ce x l || are-free-in-term ce (trie-remove x X) t
are-free-in-type ce x (TpApp t t') = are-free-in-type ce x t || are-free-in-type ce x t'
are-free-in-type ce x (TpAppt t t') = are-free-in-type ce x t || are-free-in-term ce x t'
are-free-in-type ce x (TpArrow t _ t') = are-free-in-type ce x t || are-free-in-type ce x t'
are-free-in-type ce x (TpEq _ t t' _) = are-free-in-term ce x t || are-free-in-term ce x t'
are-free-in-type ce x (TpParens x₁ t x₂) = are-free-in-type ce x t
are-free-in-type ce x (TpVar _ "_") = ff
are-free-in-type ce x (TpVar _ x') = trie-contains x x'
are-free-in-type ce x (NoSpans t _) = are-free-in-type ce x t
are-free-in-type ce x (TpHole _) = ff

are-free-in-kind ce x (KndArrow k k') = are-free-in-kind ce x k || are-free-in-kind ce x k'
are-free-in-kind ce x (KndParens x₁ k x₂) = are-free-in-kind ce x k
are-free-in-kind ce x (KndPi _ _ x' atk k) = are-free-in-tk ce x atk || are-free-in-kind ce (trie-remove x x') k
are-free-in-kind ce x (KndTpArrow t k) = are-free-in-type ce x t || are-free-in-kind ce x k
are-free-in-kind ce x (KndVar _ x' ys) = trie-contains x x' || are-free-in-args ce x ys
are-free-in-kind ce x (Star x₁) = ff

are-free-in-args ce x (ArgsCons (TermArg y) ys) = are-free-in-term ce x y || are-free-in-args ce x ys
are-free-in-args ce x (ArgsCons (TypeArg y) ys) = are-free-in-type ce x y || are-free-in-args ce x ys
are-free-in-args ce x ArgsNil = ff

are-free-in-optClass ce x NoClass = ff
are-free-in-optClass ce x (SomeClass atk) = are-free-in-tk ce x atk

-- are-free-in-optType ce x NoType = ff
-- are-free-in-optType ce x (SomeType t) = are-free-in-type ce x t

are-free-in-maybeCheckType ce x NoCheckType = ff
are-free-in-maybeCheckType ce x (Type t) = are-free-in-type ce x t

are-free-in-optTerm ce x NoTerm = ff
are-free-in-optTerm ce x (SomeTerm t _) = are-free-in-term ce x t

are-free-in-optGuide ce x NoGuide = ff
are-free-in-optGuide ce x (Guide pi v tp) = are-free-in-type ce (trie-remove x v) tp

are-free-in-tk ce x (Tkt t) = are-free-in-type ce x t
are-free-in-tk ce x (Tkk k) = are-free-in-kind ce x k

are-free-in-liftingType ce x (LiftArrow l l') = are-free-in-liftingType ce x l || are-free-in-liftingType ce x l'
are-free-in-liftingType ce x (LiftParens x₁ l x₂) = are-free-in-liftingType ce x l
are-free-in-liftingType ce x (LiftPi _ x' t l) =
  are-free-in-type ce x t || are-free-in-liftingType ce (trie-remove x x') l
are-free-in-liftingType ce x (LiftStar x₁) = ff
are-free-in-liftingType ce x (LiftTpArrow t l) = are-free-in-type ce x t || are-free-in-liftingType ce x l

are-free-in-maybeAtype ce x NoAtype = ff
are-free-in-maybeAtype ce x (Atype T) = are-free-in-type ce x T

are-free-in : {ed : exprd} → are-free-e → stringset → ⟦ ed ⟧ → 𝔹
are-free-in{TERM} e x t = are-free-in-term e x t
are-free-in{ARG} e x (TermArg t) = are-free-in-term e x t
are-free-in{TYPE} e x t = are-free-in-type e x t 
are-free-in{ARG} e x (TypeArg t) = are-free-in-type e x t
are-free-in{KIND} e x t = are-free-in-kind e x t
are-free-in{TK} e x t = are-free-in-tk e x t
are-free-in{LIFTINGTYPE} e x t = are-free-in-liftingType e x t 
are-free-in{QUALIF} e x (x' , as) = trie-contains x x' || are-free-in-args e x as

is-free-in : {ed : exprd} → are-free-e → var → ⟦ ed ⟧ → 𝔹
is-free-in{TERM} e x t = are-free-in-term e (stringset-singleton x) t
is-free-in{ARG} e x (TermArg t) = are-free-in-term e (stringset-singleton x) t
is-free-in{TYPE} e x t = are-free-in-type e (stringset-singleton x) t 
is-free-in{ARG} e x (TypeArg t) = are-free-in-type e (stringset-singleton x) t
is-free-in{KIND} e x t = are-free-in-kind e (stringset-singleton x) t 
is-free-in{LIFTINGTYPE} e x t = are-free-in-liftingType e (stringset-singleton x) t 
is-free-in{QUALIF} e x (x' , as) = x =string x' || are-free-in-args e (stringset-singleton x) as
is-free-in{TK} e x t = are-free-in-tk e (stringset-singleton x) t

abs-tk : lam → var → posinfo → tk → type → type
abs-tk l x pi (Tkk k) tp = Abs posinfo-gen All pi x (Tkk k) tp
abs-tk ErasedLambda x pi (Tkt tp') tp = Abs posinfo-gen All pi x (Tkt tp') tp
abs-tk KeptLambda x pi (Tkt tp') tp with are-free-in check-erased (stringset-singleton x) tp 
abs-tk KeptLambda x pi (Tkt tp') tp | tt = Abs posinfo-gen Pi pi x (Tkt tp') tp
abs-tk KeptLambda x pi (Tkt tp') tp | ff = TpArrow tp' UnerasedArrow  tp

absk-tk : var → posinfo → tk → kind → kind
absk-tk x pi atk k with are-free-in check-erased (stringset-singleton (pi % x)) k
absk-tk x pi atk k | tt = KndPi posinfo-gen pi x atk k
absk-tk x pi (Tkt tp) k | ff = KndTpArrow tp k
absk-tk x pi (Tkk k') k | ff = KndArrow k' k

data abs  : Set where
  mk-abs : posinfo → binder → posinfo → var → tk → (var-free-in-body : 𝔹) → type → abs 

to-abs : type → maybe abs
to-abs (Abs pi b pi' x atk tp) = just (mk-abs pi b pi' x atk (are-free-in check-erased (stringset-singleton x) tp) tp)
to-abs (TpArrow tp1 ErasedArrow tp2) = just (mk-abs posinfo-gen All posinfo-gen dummy-var (Tkt tp1) ff tp2)
to-abs (TpArrow tp1 UnerasedArrow tp2) = just (mk-abs posinfo-gen Pi posinfo-gen dummy-var (Tkt tp1) ff tp2)
to-abs _ = nothing

data absk  : Set where
  mk-absk : posinfo → posinfo → var → tk → (var-free-in-body : 𝔹) → kind → absk 

to-absk : kind → maybe absk
to-absk (KndPi pi pi' x atk k) = just (mk-absk pi pi' x atk (are-free-in check-erased (stringset-singleton x) k) k)
to-absk (KndArrow k1 k2) = just (mk-absk posinfo-gen posinfo-gen dummy-var (Tkk k1) ff k2)
to-absk (KndTpArrow tp k) = just (mk-absk posinfo-gen posinfo-gen dummy-var (Tkt tp) ff k)
to-absk _ = nothing

