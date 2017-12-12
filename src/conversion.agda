module conversion where

open import lib

open import cedille-types
open import ctxt
open import is-free
open import lift
open import rename
open import subst
open import syntax-util
open import to-string

{- Some notes:

   -- hnf{TERM} implements erasure as well as normalization.

   -- hnf{TYPE} does not descend into terms.

   -- definitions are assumed to be in hnf
-}

data unfolding : Set where
  no-unfolding : unfolding
  unfold : (unfold-all : 𝔹) {- if ff we unfold just the head -} → 
           (unfold-rec : 𝔹) {- if tt we unfold recursive type definitions -} → 
           (dampen-after-head-beta : 𝔹) {- if tt we will not unfold definitions after a head beta reduction -} → 
           unfolding

unfold-all : unfolding
unfold-all = unfold tt ff ff 

unfold-head : unfolding
unfold-head = unfold ff ff ff 

unfold-head-rec-defs : unfolding
unfold-head-rec-defs = unfold ff tt ff 

unfold-head-one : unfolding
unfold-head-one = unfold ff ff tt 

unfold-dampen : (after-head-beta : 𝔹) → unfolding → unfolding
unfold-dampen _ no-unfolding = no-unfolding
unfold-dampen _ (unfold tt b b') = unfold tt b b' -- we do not dampen unfolding when unfolding everywhere
unfold-dampen tt (unfold ff b tt) = no-unfolding
unfold-dampen tt (unfold ff b ff) = (unfold ff b ff)
unfold-dampen ff _ = no-unfolding

unfold-dampen-rec : (after-head-beta : 𝔹) → unfolding → unfolding
unfold-dampen-rec _ no-unfolding = no-unfolding
unfold-dampen-rec ff (unfold b _ b') = unfold b ff b'
unfold-dampen-rec tt (unfold b b' b'') = unfold b b' b''

conv-t : Set → Set
conv-t T = ctxt → T → T → 𝔹

{-# TERMINATING #-}
conv-term : conv-t term
conv-type : conv-t type 
conv-kind : conv-t kind
hnf : {ed : exprd} → ctxt → (u : unfolding) → ⟦ ed ⟧ → (is-head : 𝔹) → ⟦ ed ⟧ 
conv-term-norm : conv-t term
conv-type-norm : conv-t type
conv-kind-norm : conv-t kind

hnf-optClass : ctxt → unfolding → optClass → optClass
hnf-tk : ctxt → unfolding → tk → tk
conv-tk : conv-t tk
conv-liftingType : conv-t liftingType
conv-optClass : conv-t optClass
conv-optType : conv-t optType
conv-tty* : conv-t (𝕃 tty)

conv-term Γ t t' = conv-term-norm Γ (hnf Γ unfold-head t tt) (hnf Γ unfold-head t' tt)
conv-type Γ t t' = conv-type-norm Γ (hnf Γ unfold-head t tt) (hnf Γ unfold-head t' tt)
conv-kind Γ k k' = conv-kind-norm Γ (hnf Γ unfold-head k tt) (hnf Γ unfold-head k' tt)

-- is-head is only used in hnf{TYPE}
hnf{TERM} Γ no-unfolding e hd = erase-term e
hnf{TERM} Γ u (Parens _ t _) hd = hnf Γ u t hd
hnf{TERM} Γ u (App t1 Erased t2) hd = hnf Γ u t1 hd
hnf{TERM} Γ u (App t1 NotErased t2) hd with hnf Γ u t1 hd
hnf{TERM} Γ u (App _ NotErased t2) hd | Lam _ _ _ x _ t1 = hnf Γ (unfold-dampen tt u) (subst-term Γ t2 x t1) hd
hnf{TERM} Γ u (App _ NotErased t2) hd | t1 = App t1 NotErased (hnf Γ (unfold-dampen ff u) t2 hd)
hnf{TERM} Γ u (Lam _ ErasedLambda _ _ _ t) hd = hnf Γ u t hd
hnf{TERM} Γ u (Lam pi KeptLambda pi' x oc t) hd with hnf (ctxt-var-decl pi' x Γ) u t hd
hnf{TERM} Γ u (Lam pi KeptLambda pi' x oc t) hd | (App t' NotErased (Var _ x')) with x =string x' && ~ (is-free-in skip-erased x t')
hnf{TERM} Γ u (Lam pi KeptLambda pi' x oc t) hd | (App t' NotErased (Var _ x')) | tt = t' -- eta-contraction
hnf{TERM} Γ u (Lam pi KeptLambda pi' x oc t) hd | (App t' NotErased (Var pi'' x')) | _ = 
  Lam pi KeptLambda pi' x NoClass (App t' NotErased (Var pi'' x'))
hnf{TERM} Γ u (Lam pi KeptLambda pi' x oc t) hd | t' = Lam pi KeptLambda pi' x NoClass t'
hnf{TERM} Γ u (Let _ (DefTerm _ x _ t) t') hd = hnf Γ u (subst-term Γ t x t') hd 
hnf{TERM} Γ u (Let _ (DefType _ _ _ _) t') hd = hnf Γ u t' hd 
hnf{TERM} Γ (unfold _ _ _ ) (Var pi x) hd with ctxt-lookup-term-var-def Γ x
hnf{TERM} Γ (unfold _ _ _ ) (Var pi x) hd | nothing = Var pi x
hnf{TERM} Γ (unfold ff _ _ ) (Var pi x) hd | just t = t -- definitions should be stored in hnf
hnf{TERM} Γ (unfold tt b b' ) (Var pi x) hd | just t = hnf Γ (unfold tt b b') t hd -- this might not be fully normalized, only head-normalized
hnf{TERM} Γ u (AppTp t tp) hd = hnf Γ u t hd
hnf{TERM} Γ u (Sigma pi t) hd = hnf Γ u t hd
hnf{TERM} Γ u (Epsilon _ _ _ t) hd = hnf Γ u t hd
hnf{TERM} Γ u (IotaPair _ t1 t2 _ _) hd = hnf Γ u t1 hd
hnf{TERM} Γ u (IotaProj t _ _) hd = hnf Γ u t hd
hnf{TERM} Γ u (Rho pi _ t t') hd = hnf Γ u t' hd
hnf{TERM} Γ u (Chi pi T t') hd = hnf Γ u t' hd
hnf{TERM} Γ u (Theta pi u' t ls) hd = hnf Γ u (App*' t (erase-lterms u' ls)) hd
hnf{TERM} Γ u (Beta _ (SomeTerm t _)) hd = hnf Γ u t hd
hnf{TERM} Γ u (Beta _ NoTerm) hd = id-term
hnf{TERM} Γ u x hd = x

hnf{TYPE} Γ no-unfolding e _ = e
hnf{TYPE} Γ u (TpParens _ t _) hd = hnf Γ u t hd
hnf{TYPE} Γ u (NoSpans t _)  hd = hnf Γ u t hd
hnf{TYPE} Γ (unfold b b' _) (TpVar pi x) ff  = TpVar pi x 
hnf{TYPE} Γ (unfold b b' _) (TpVar _ x) tt with ctxt-lookup-type-var-def Γ x
hnf{TYPE} Γ (unfold b b' _) (TpVar pi x) tt | just tp = tp
hnf{TYPE} Γ (unfold b ff _) (TpVar pi x) tt | nothing = TpVar pi x
hnf{TYPE} Γ (unfold b tt _) (TpVar pi x) tt | nothing = TpVar pi x
hnf{TYPE} Γ u (TpAppt tp t) hd with hnf Γ u tp hd
hnf{TYPE} Γ u (TpAppt _ t) hd  | TpLambda _ _ x _ tp = hnf Γ u (subst-type Γ t x tp) hd
hnf{TYPE} Γ u (TpAppt _ t) hd | tp = TpAppt tp (erase-term t)
hnf{TYPE} Γ u (TpApp tp tp') hd with hnf Γ u tp hd
hnf{TYPE} Γ u (TpApp _ tp') hd | TpLambda _ _ x _ tp = hnf Γ (unfold-dampen-rec tt u) (subst-type Γ tp' x tp) hd 
hnf{TYPE} Γ u (TpApp _ tp') hd | tp with hnf Γ (unfold-dampen-rec ff u) tp' hd 
hnf{TYPE} Γ u (TpApp _ _) hd | tp | tp' = try-pull-lift-types tp tp'

  {- given (T1 T2), with T1 and T2 types, see if we can pull a lifting operation from the heads of T1 and T2 to
     surround the entire application.  If not, just return (T1 T2). -}
  where try-pull-lift-types : type → type → type
        try-pull-lift-types tp1 tp2 with decompose-tpapps tp1 | decompose-tpapps (hnf Γ u tp2 tt)
        try-pull-lift-types tp1 tp2 | Lft _ _ X t l , args1 | Lft _ _ X' t' l' , args2 =
          if conv-tty* Γ args1 args2 then
            try-pull-term-in Γ t l (length args1) [] []
          else
            TpApp tp1 tp2

          where try-pull-term-in : ctxt → term → liftingType → ℕ → 𝕃 var → 𝕃 liftingType → type
                try-pull-term-in Γ t (LiftParens _ l _) n vars ltps = try-pull-term-in Γ t l n vars ltps 
                try-pull-term-in Γ t (LiftArrow _ l) 0 vars ltps = 
                  recompose-tpapps 
                    (Lft posinfo-gen posinfo-gen X
                      (Lam* vars (hnf Γ no-unfolding (App t NotErased (App* t' (map (λ v → NotErased , mvar v) vars))) tt))
                      (LiftArrow* ltps l) , args1)
                try-pull-term-in Γ (Lam _ _ pi' x _ t) (LiftArrow l1 l2) (suc n) vars ltps =
                  try-pull-term-in (ctxt-var-decl pi' x Γ) t l2 n (x :: vars) (l1 :: ltps) 
                try-pull-term-in Γ t (LiftArrow l1 l2) (suc n) vars ltps =
                  let x = fresh-var "x" (ctxt-binds-var Γ) empty-renamectxt in
                    try-pull-term-in (ctxt-var-decl posinfo-gen x Γ) (App t NotErased (mvar x)) l2 n (x :: vars) (l1 :: ltps) 
                try-pull-term-in Γ t l n vars ltps = TpApp tp1 tp2

        try-pull-lift-types tp1 tp2 | _ | _ = TpApp tp1 tp2


hnf{TYPE} Γ u (Abs pi b pi' x atk tp) _ with Abs pi b pi' x atk (hnf (ctxt-var-decl pi' x Γ) (unfold-dampen-rec ff u) tp ff)
hnf{TYPE} Γ u (Abs pi b pi' x atk tp) _ | tp' with to-abs tp'
hnf{TYPE} Γ u (Abs _ _ _ _ _ _) _ | tp'' | just (mk-abs pi b pi' x atk tt {- x is free in tp -} tp) = Abs pi b pi' x atk tp
hnf{TYPE} Γ u (Abs _ _ _ _ _ _) _ | tp'' | just (mk-abs pi b pi' x (Tkk k) ff tp) = Abs pi b pi' x (Tkk k) tp
hnf{TYPE} Γ u (Abs _ _ _ _ _ _) _ | tp'' | just (mk-abs pi All pi' x (Tkt tp') ff tp) = TpArrow tp' ErasedArrow tp
hnf{TYPE} Γ u (Abs _ _ _ _ _ _) _ | tp'' | just (mk-abs pi Pi pi' x (Tkt tp') ff tp) = TpArrow tp' UnerasedArrow tp
hnf{TYPE} Γ u (Abs _ _ _ _ _ _) _ | tp'' | nothing = tp''
hnf{TYPE} Γ u (TpArrow tp1 arrowtype tp2) _ = TpArrow (hnf Γ (unfold-dampen-rec ff u) tp1 ff) arrowtype (hnf Γ (unfold-dampen-rec ff u) tp2 ff)
hnf{TYPE} Γ u (TpEq t1 t2) _ = TpEq (erase-term t1) (erase-term t2)
hnf{TYPE} Γ u (TpLambda pi pi' x atk tp) _ = 
  TpLambda pi pi' x (hnf-tk Γ (unfold-dampen-rec ff u) atk) (hnf (ctxt-var-decl pi' x Γ) (unfold-dampen-rec ff u) tp ff)
hnf{TYPE} Γ u (Lft pi pi' y t l) _ = 
 let t = hnf (ctxt-var-decl pi' y Γ) u t tt in
   do-lift Γ (Lft pi pi' y t l) y l t
hnf{TYPE} Γ u x _ = x

hnf{KIND} Γ no-unfolding e hd = e
hnf{KIND} Γ u (KndParens _ k _) hd = hnf Γ u k hd
hnf{KIND} Γ (unfold _ _ _) (KndVar pi x ys) _ with ctxt-lookup-kind-var-def Γ x 
... | nothing = KndVar pi x ys
... | just (ps , k) = do-subst ys ps k
  where do-subst : args → params → kind → kind
        do-subst (ArgsCons (TermArg t) ys) (ParamsCons (Decl _ _ x _ _) ps) k = do-subst ys ps (subst-kind Γ t x k)
        do-subst (ArgsCons (TypeArg t) ys) (ParamsCons (Decl _ _ x _ _) ps) k = do-subst ys ps (subst-kind Γ t x k)
        do-subst _ _ k = k -- should not happen 

hnf{KIND} Γ u (KndPi pi pi' x atk k) hd =
    if is-free-in check-erased x k then
      (KndPi pi pi' x atk k)
    else
      tk-arrow-kind atk k
hnf{KIND} Γ u x hd = x

hnf{LIFTINGTYPE} Γ u x hd = x
hnf{QUALIF} Γ u x hd = x
hnf{ARG} Γ u x hd = x

hnf-tk Γ u (Tkk k) = Tkk (hnf Γ u k tt)
hnf-tk Γ u (Tkt tp) = Tkt (hnf Γ u tp ff)

hnf-optClass Γ u NoClass = NoClass
hnf-optClass Γ u (SomeClass atk) = SomeClass (hnf-tk Γ u atk)

{- this function reduces a term to "head-applicative" normal form,
   which avoids unfolding definitions if they would lead to a top-level
   lambda-abstraction or top-level application headed by a variable for which we
   do not have a (global) definition. -}
{-# TERMINATING #-}
hanf : ctxt → term → term
hanf Γ t with hnf Γ unfold-head-one t tt
hanf Γ t | t' with decompose-apps t'
hanf Γ t | t' | (Var _ x) , [] = t'
hanf Γ t | t' | (Var _ x) , args with ctxt-lookup-term-var-def Γ x 
hanf Γ t | t' | (Var _ x) , args | nothing = t'
hanf Γ t | t' | (Var _ x) , args | just _ = hanf Γ t'
hanf Γ t | t' | h , args {- h could be a Lambda if args is [] -} = t

-- unfold across the term-type barrier
hnf-term-type : ctxt → type → type
hnf-term-type Γ (TpEq t1 t2) = TpEq (hanf Γ t1) (hanf Γ t2)
hnf-term-type Γ (TpAppt tp t) = hnf Γ unfold-head (TpAppt tp (hanf Γ t)) tt
hnf-term-type Γ tp = hnf Γ unfold-head tp tt

conv-term-norm Γ (Var _ x) (Var _ x') = ctxt-eq-rep Γ x x'
-- hnf implements erasure for terms, so we can ignore some subterms for App and Lam cases below
conv-term-norm Γ (App t1 m t2) (App t1' m' t2') = conv-term-norm Γ t1 t1' && conv-term Γ t2 t2'
conv-term-norm Γ (Lam _ l pi x oc t) (Lam _ l' pi' x' oc' t') = conv-term (ctxt-rename pi x x' (ctxt-var-decl-if pi' x' Γ)) t t'
conv-term-norm Γ (Hole _) _ = tt
conv-term-norm Γ _ (Hole _) = tt
conv-term-norm Γ (Beta _ NoTerm) (Beta _ NoTerm) = tt
conv-term-norm Γ (Beta _ (SomeTerm t _)) (Beta _ (SomeTerm t' _)) = conv-term Γ t t'
conv-term-norm Γ (Beta _ _) (Beta _ _) = ff
{- it can happen that a term is equal to a lambda abstraction in head-normal form,
   if that lambda-abstraction would eta-contract following some further beta-reductions.
   We implement this here by implicitly eta-expanding the variable and continuing
   the comparison.

   A simple example is 

       λ v . t ((λ a . a) v) ≃ t
 -}
conv-term-norm Γ (Lam pi1 l pi2 x oc t) t' = conv-term (ctxt-rename pi2 x x Γ) t (App t' NotErased (Var pi2 x))
conv-term-norm Γ t' (Lam pi1 l pi2 x oc t) = conv-term (ctxt-rename pi2 x x Γ) (App t' NotErased (Var pi2 x)) t 
conv-term-norm Γ _ _ = ff

conv-type-norm Γ (TpVar _ x) (TpVar _ x') = ctxt-eq-rep Γ x x'
conv-type-norm Γ (TpApp t1 t2) (TpApp t1' t2') = conv-type-norm Γ t1 t1' && conv-type Γ t2 t2'
conv-type-norm Γ (TpAppt t1 t2) (TpAppt t1' t2') = conv-type-norm Γ t1 t1' && conv-term Γ t2 t2'
conv-type-norm Γ (Abs _ b pi x atk tp) (Abs _ b' pi' x' atk' tp') = 
  eq-binder b b' && conv-tk Γ atk atk' && conv-type (ctxt-rename pi x x' (ctxt-var-decl-if pi' x' Γ)) tp tp'
conv-type-norm Γ (TpArrow tp1 a1 tp2) (TpArrow tp1' a2  tp2') = eq-arrowtype a1 a2 && conv-type Γ tp1 tp1' && conv-type Γ tp2 tp2'
conv-type-norm Γ (TpArrow tp1 a tp2) (Abs _ b _ _ (Tkt tp1') tp2') = arrowtype-matches-binder a b && conv-type Γ tp1 tp1' && conv-type Γ tp2 tp2'
conv-type-norm Γ (Abs _ b _ _ (Tkt tp1) tp2) (TpArrow tp1' a tp2') = arrowtype-matches-binder a b && conv-type Γ tp1 tp1' && conv-type Γ tp2 tp2'
conv-type-norm Γ (Iota _ pi x m tp) (Iota _ pi' x' m' tp') = 
  conv-optType Γ m m' && conv-type (ctxt-rename pi x x' (ctxt-var-decl-if pi' x' Γ)) tp tp'
conv-type-norm Γ (TpEq t1 t2) (TpEq t1' t2') = conv-term Γ t1 t1' && conv-term Γ t2 t2'
conv-type-norm Γ (Lft _ pi x t l) (Lft _ pi' x' t' l') =
  conv-liftingType Γ l l' && conv-term (ctxt-rename pi x x' (ctxt-var-decl-if pi' x' Γ)) t t'
conv-type-norm Γ (TpLambda _ pi x atk tp) (TpLambda _ pi' x' atk' tp') =
  conv-tk Γ atk atk' && conv-type (ctxt-rename pi x x' (ctxt-var-decl-if pi' x' Γ)) tp tp'
conv-type-norm Γ _ _ = ff 

{- even though hnf turns Pi-kinds where the variable is not free in the body into arrow kinds,
   we still need to check off-cases, because normalizing the body of a kind could cause the
   bound variable to be erased (hence allowing it to match an arrow kind). -}
conv-kind-norm Γ (KndArrow k k₁) (KndArrow k' k'') = conv-kind Γ k k' && conv-kind Γ k₁ k''
conv-kind-norm Γ (KndArrow k k₁) (KndPi _ _ x (Tkk k') k'') = conv-kind Γ k k' && conv-kind Γ k₁ k''
conv-kind-norm Γ (KndArrow k k₁) _ = ff
conv-kind-norm Γ (KndPi _ _ x (Tkk k₁) k) (KndArrow k' k'') = conv-kind Γ k₁ k' && conv-kind Γ k k''
conv-kind-norm Γ (KndPi _ pi x atk k) (KndPi _ pi' x' atk' k'') = 
    conv-tk Γ atk atk' && conv-kind (ctxt-rename pi x x' (ctxt-var-decl-if pi' x' Γ)) k k''
conv-kind-norm Γ (KndPi _ _ x (Tkt t) k) (KndTpArrow t' k'') = conv-type Γ t t' && conv-kind Γ k k''
conv-kind-norm Γ (KndPi _ _ x (Tkt t) k) _ = ff
conv-kind-norm Γ (KndPi _ _ x (Tkk k') k) _ = ff
conv-kind-norm Γ (KndTpArrow t k) (KndTpArrow t' k') = conv-type Γ t t' && conv-kind Γ k k'
conv-kind-norm Γ (KndTpArrow t k) (KndPi _ _ x (Tkt t') k') = conv-type Γ t t' && conv-kind Γ k k'
conv-kind-norm Γ (KndTpArrow t k) _ = ff
conv-kind-norm Γ (Star x) (Star x') = tt
conv-kind-norm Γ (Star x) _ = ff
conv-kind-norm Γ _ _ = ff -- should not happen, since the kinds are in hnf

conv-tk Γ (Tkk k) (Tkk k') = conv-kind Γ k k'
conv-tk Γ (Tkt t) (Tkt t') = conv-type Γ t t'
conv-tk Γ _ _ = ff

conv-liftingType Γ l l' = conv-kind Γ (liftingType-to-kind l) (liftingType-to-kind l')

conv-optClass Γ NoClass NoClass = tt
conv-optClass Γ (SomeClass x) (SomeClass x') = conv-tk Γ x x'
conv-optClass Γ _ _ = ff

conv-optType Γ NoType NoType = tt
conv-optType Γ (SomeType x) (SomeType x') = conv-type Γ x x'
conv-optType Γ _ _ = ff

conv-tty* Γ [] [] = tt
conv-tty* Γ (tterm t :: args) (tterm t' :: args') = conv-term Γ t t' && conv-tty* Γ args args'
conv-tty* Γ (ttype t :: args) (ttype t' :: args') = conv-type Γ t t' && conv-tty* Γ args args'
conv-tty* Γ _ _ = ff

hnf-qualif-term : ctxt → term → term
hnf-qualif-term Γ t = hnf Γ unfold-head (qualif-term Γ t) tt

hnf-qualif-type : ctxt → type → type
hnf-qualif-type Γ t = hnf Γ unfold-head (qualif-type Γ t) tt

hnf-qualif-kind : ctxt → kind → kind
hnf-qualif-kind Γ t = hnf Γ unfold-head (qualif-kind Γ t) tt
