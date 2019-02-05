module erase where

open import syntax-util
open import lib
open import cedille-types
open import general-util
open import constants
open import is-free

{-# TERMINATING #-}
erase : { ed : exprd } → ⟦ ed ⟧ → ⟦ ed ⟧
erase-term : term → term
erase-type : type → type
erase-kind : kind → kind
erase-lterms : term → lterms → term
erase-tk : tk → tk
erase-liftingType : liftingType → liftingType
erase-cases : cases → cases
erase-case : case → case
erase-caseArgs : caseArgs → caseArgs
erase-term-args : args → 𝕃 term

erase-if : 𝔹 → { ed : exprd } → ⟦ ed ⟧ → ⟦ ed ⟧
erase-if tt = erase
erase-if ff = id

erase-term (Parens _ t _) = erase-term t
erase-term (App t1 Erased t2) = erase-term t1
erase-term (App t1 NotErased t2) = App (erase-term t1) NotErased (erase-term t2)
erase-term (AppTp t tp) = erase-term t
erase-term (Lam _ Erased _ _ _ t) = erase-term t
erase-term (Lam _ NotErased _ x oc t) = Lam posinfo-gen NotErased posinfo-gen x NoClass (erase-term t)
erase-term (Let _ NotErased (DefTerm _ x _ t) t') =
  let body = erase-term t' 
  in if is-free-in skip-erased x t'
     then Let posinfo-gen ff (DefTerm posinfo-gen x NoType (erase-term t)) body
     -- if x does not occur in an unerase position in t', then the binding is irrelevant in the erasure
     else body
erase-term (Let _ Erased (DefTerm _ x _ t) t') = erase-term t'
erase-term (Let _ _ (DefType _ _ _ _) t) = erase-term t
erase-term (Open _ _ _ _ t) = erase-term t
erase-term (Var _ x) = Var posinfo-gen x
erase-term (Beta _ _ NoTerm) = id-term
erase-term (Beta _ _ (SomeTerm t _)) = erase-term t
erase-term (IotaPair _ t1 t2 _ _) = erase-term t1
erase-term (IotaProj t n _) = erase-term t
erase-term (Epsilon _ lr _ t) = erase-term t
erase-term (Sigma _ t) = erase-term t
erase-term (Hole pi) = Hole pi -- Retain position, so jumping to hole works
erase-term (Phi _ t t₁ t₂ _) = erase-term t₂
erase-term (Rho _ _ _ t _ t') = erase-term t'
erase-term (Chi _ T t') = erase-term t'
erase-term (Delta _ T t) = id-term
erase-term (Theta _ u t ls) = erase-lterms (erase-term t) ls
erase-term (Mu _ _ x t ot _ c _) = Mu posinfo-gen posinfo-gen x (erase-term t) NoType posinfo-gen (erase-cases c) posinfo-gen
erase-term (Mu' _ _ t _ _ c _)  = Mu' posinfo-gen NoTerm (erase-term t) NoType posinfo-gen (erase-cases c) posinfo-gen

erase-cases = map erase-case

erase-case (Case _ x as t) = Case posinfo-gen x (erase-caseArgs as) (erase-term t)

erase-caseArgs [] = []
erase-caseArgs ((CaseTermArg pi NotErased t) :: as) = CaseTermArg posinfo-gen NotErased t :: erase-caseArgs as
erase-caseArgs (_ :: as) = erase-caseArgs as

erase-term-args [] = []
erase-term-args (TermArg NotErased t :: as) = erase t :: erase-term-args as
erase-term-args (_ :: as) = erase-term-args as

-- Only erases TERMS in types, leaving the structure of types the same
erase-type (Abs _ b _ v atk tp) = Abs posinfo-gen b posinfo-gen v (erase-tk atk) (erase-type tp)
erase-type (Iota _ _ v otp tp) = Iota posinfo-gen posinfo-gen v (erase-type otp) (erase-type tp)
erase-type (Lft _ _ v t lt) = Lft posinfo-gen posinfo-gen v (erase-term t) (erase-liftingType lt)
erase-type (NoSpans tp _) = NoSpans (erase-type tp) posinfo-gen
erase-type (TpApp tp tp') = TpApp (erase-type tp) (erase-type tp')
erase-type (TpAppt tp t) = TpAppt (erase-type tp) (erase-term t)
erase-type (TpArrow tp at tp') = TpArrow (erase-type tp) at (erase-type tp')
erase-type (TpEq _ t t' _) = TpEq posinfo-gen (erase-term t) (erase-term t') posinfo-gen
erase-type (TpLambda _ _ v atk tp) = TpLambda posinfo-gen posinfo-gen v (erase-tk atk) (erase-type tp)
erase-type (TpParens _ tp _) = erase-type tp
erase-type (TpHole pi) = TpHole pi -- Retain position, so jumping to hole works
erase-type (TpVar _ x) = TpVar posinfo-gen x
erase-type (TpLet _ (DefTerm _ x _ t) T) = TpLet posinfo-gen (DefTerm posinfo-gen x NoType (erase-term t)) (erase-type T)
erase-type (TpLet _ (DefType _ x k T) T') = TpLet posinfo-gen (DefType posinfo-gen x (erase-kind k) (erase-type T)) (erase-type T')

-- Only erases TERMS in types in kinds, leaving the structure of kinds and types in those kinds the same
erase-kind (KndArrow k k') = KndArrow (erase-kind k) (erase-kind k')
erase-kind (KndParens _ k _) = erase-kind k
erase-kind (KndPi _ _ v atk k) = KndPi posinfo-gen posinfo-gen v (erase-tk atk) (erase-kind k)
erase-kind (KndTpArrow tp k) = KndTpArrow (erase-type tp) (erase-kind k)
erase-kind (KndVar _ x ps) = KndVar posinfo-gen x ps
erase-kind (Star _) = Star posinfo-gen

erase{TERM} t = erase-term t
erase{TYPE} tp = erase-type tp
erase{KIND} k = erase-kind k
erase{LIFTINGTYPE} lt = erase-liftingType lt
erase{TK} atk = erase-tk atk
erase{ARG} a = a
erase{QUALIF} q = q

erase-tk (Tkt tp) = Tkt (erase-type tp)
erase-tk (Tkk k) = Tkk (erase-kind k)

erase-liftingType (LiftArrow lt lt') = LiftArrow (erase-liftingType lt) (erase-liftingType lt')
erase-liftingType (LiftParens _ lt _) = erase-liftingType lt
erase-liftingType (LiftPi _ v tp lt) = LiftPi posinfo-gen v (erase-type tp) (erase-liftingType lt)
erase-liftingType (LiftTpArrow tp lt) = LiftTpArrow (erase-type tp) (erase-liftingType lt)
erase-liftingType lt = lt

erase-lterms t [] = t
erase-lterms t ((Lterm Erased t') :: ls) = erase-lterms t ls
erase-lterms t ((Lterm NotErased t') :: ls) = erase-lterms (App t NotErased (erase-term t')) ls
