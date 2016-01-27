module conversion where

open import lib

open import cedille-types
open import ctxt
open import is-free
open import lift
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
           unfolding

unfold-all : unfolding
unfold-all = unfold tt ff

unfold-head : unfolding
unfold-head = unfold ff ff

unfold-head-rec-defs : unfolding
unfold-head-rec-defs = unfold ff tt

unfold-dampen : unfolding → unfolding
unfold-dampen no-unfolding = no-unfolding
unfold-dampen (unfold ff _) = no-unfolding
unfold-dampen (unfold tt b) = unfold tt b -- we do not dampen unfolding when unfolding everywhere

{-# NO_TERMINATION_CHECK #-}
conv-term : ctxt → term → term → 𝔹
conv-type : ctxt → type → type → 𝔹
conv-kind : ctxt → kind → kind → 𝔹
hnf : {ed : exprd} → ctxt → (u : unfolding) → ⟦ ed ⟧ → ⟦ ed ⟧
conv-term-norm : ctxt → term → term → 𝔹
conv-type-norm : ctxt → type → type → 𝔹
conv-kind-norm : ctxt → kind → kind → 𝔹

hnf-optClass : ctxt → unfolding → optClass → optClass
hnf-tk : ctxt → unfolding → tk → tk
conv-tk : ctxt → tk → tk → 𝔹
conv-liftingType : ctxt → liftingType → liftingType → 𝔹
conv-optClass : ctxt → optClass → optClass → 𝔹
conv-tty* : ctxt → 𝕃 tty → 𝕃 tty → 𝔹

conv-term Γ t t' = conv-term-norm Γ (hnf Γ unfold-head t) (hnf Γ unfold-head t')
conv-type Γ t t' = conv-type-norm Γ (hnf Γ unfold-head t) (hnf Γ unfold-head t')
conv-kind Γ k k' = conv-kind-norm Γ (hnf Γ unfold-head k) (hnf Γ unfold-head k')

hnf{TERM} Γ u (Parens _ t _) = hnf Γ u t
hnf{TERM} Γ u (App t1 Erased t2) = hnf Γ u t1
hnf{TERM} Γ u (App t1 NotErased t2) with hnf Γ u t1
hnf{TERM} Γ u (App _ NotErased t2) | Lam _ _ _ x _ t1 = hnf Γ u (subst-term Γ t2 x t1)
hnf{TERM} Γ u (App _ NotErased t2) | t1 = App t1 NotErased (hnf Γ (unfold-dampen u) t2)
hnf{TERM} Γ u (Lam _ ErasedLambda _ _ _ t) = hnf Γ u t
hnf{TERM} Γ u (Lam pi KeptLambda pi' x oc t) with hnf (ctxt-var-decl x Γ) u t
hnf{TERM} Γ u (Lam pi KeptLambda pi' x oc t) | (App t' NotErased (Var _ x')) with x =string x' && ~ (is-free-in skip-erased x t')
hnf{TERM} Γ u (Lam pi KeptLambda pi' x oc t) | (App t' NotErased (Var _ x')) | tt = t' -- eta-contraction
hnf{TERM} Γ u (Lam pi KeptLambda pi' x oc t) | (App t' NotErased (Var pi'' x')) | _ = Lam pi KeptLambda pi' x NoClass 
                                                                                       (App t' NotErased (Var pi'' x'))
hnf{TERM} Γ u (Lam pi KeptLambda pi' x oc t) | t' = Lam pi KeptLambda pi' x NoClass t'
hnf{TERM} Γ (unfold b b') (Var pi x) with ctxt-lookup-term-var-def Γ x
hnf{TERM} Γ (unfold b b') (Var pi x) | nothing = Var pi x
hnf{TERM} Γ (unfold b b') (Var pi x) | just t = t -- definitions should be stored in hnf
hnf{TERM} Γ no-unfolding (Var pi x) = Var pi x
hnf{TERM} Γ u (AppTp t tp) = hnf Γ u t

hnf{TYPE} Γ u (TpParens _ t _) = hnf Γ u t
hnf{TYPE} Γ (unfold b b') (TpVar _ x) with ctxt-lookup-type-var-def Γ x
hnf{TYPE} Γ (unfold b b') (TpVar pi x) | just tp = tp 
hnf{TYPE} Γ (unfold b ff) (TpVar pi x) | nothing = TpVar pi x
hnf{TYPE} Γ (unfold b tt) (TpVar pi x) | nothing with ctxt-lookup-type-var-rec-def Γ x
hnf{TYPE} Γ (unfold b tt) (TpVar pi x) | nothing | nothing = TpVar pi x
hnf{TYPE} Γ (unfold b tt) (TpVar pi x) | nothing | just t = t 
hnf{TYPE} Γ no-unfolding (TpVar pi x) = TpVar pi x
hnf{TYPE} Γ u (TpAppt tp t) with hnf Γ u tp
hnf{TYPE} Γ u (TpAppt _ t) | TpLambda _ _ x _ tp = hnf Γ u (subst-type Γ t x tp)
hnf{TYPE} Γ u (TpAppt _ t) | tp = TpAppt tp (erase-term t)
hnf{TYPE} Γ u (TpApp tp tp') with hnf Γ u tp
hnf{TYPE} Γ u (TpApp _ tp') | TpLambda _ _ x _ tp = hnf Γ u (subst-type Γ tp' x tp)
hnf{TYPE} Γ u (TpApp _ tp') | tp with hnf Γ (unfold-dampen u) tp' 
hnf{TYPE} Γ u (TpApp _ _) | tp | tp' = try-pull-lift-types tp tp'

  {- given (T1 T2), with T1 and T2 types, see if we can pull a lifting operation from the heads of T1 and T2 to
     surround the entire application.  If not, just return (T1 T2). -}
  where try-pull-lift-types : type → type → type
        try-pull-lift-types tp1 tp2 with decompose-tpapps tp1 | decompose-tpapps tp2
        try-pull-lift-types tp1 tp2 | Lft _ _ X t l , args1 | Lft _ _ X' t' l' , args2 =
          if conv-tty* Γ args1 args2 then
            try-pull-term-in t l (length args1) [] []
          else
            TpApp tp1 tp2
          where try-pull-term-in : term → liftingType → ℕ → 𝕃 var → 𝕃 liftingType → type
                try-pull-term-in t (LiftParens _ l _) n vars ltps = try-pull-term-in t l n vars ltps 
                try-pull-term-in t (LiftArrow _ l) 0 vars ltps = 
                  recompose-tpapps 
                    (Lft posinfo-gen posinfo-gen X (Lam* vars (hnf Γ no-unfolding (App t NotErased (App* t' (map mvar vars)))))
                      (LiftArrow* ltps l) , args1)
                try-pull-term-in (Lam _ _ _ x _ t) (LiftArrow l1 l2) (suc n) vars ltps =
                  try-pull-term-in t l2 n (x :: vars) (l1 :: ltps) 
                try-pull-term-in t l n vars ltps = TpApp tp1 tp2
        try-pull-lift-types tp1 tp2 | _ | _ = TpApp tp1 tp2

hnf{TYPE} Γ u (Abs pi b pi' x atk tp) with Abs pi b pi' x atk (hnf (ctxt-var-decl x Γ) (unfold-dampen u) tp)
hnf{TYPE} Γ u (Abs pi b pi' x atk tp) | tp' with to-abs tp'
hnf{TYPE} Γ u (Abs _ _ _ _ _ _) | tp'' | just (mk-abs pi b pi' x atk tt {- x is free in tp -} tp) = Abs pi b pi' x atk tp
hnf{TYPE} Γ u (Abs _ _ _ _ _ _) | tp'' | just (mk-abs pi b pi' x (Tkk k) ff tp) = Abs pi b pi' x (Tkk k) tp
hnf{TYPE} Γ u (Abs _ _ _ _ _ _) | tp'' | just (mk-abs pi All pi' x (Tkt tp') ff tp) = Abs pi All pi' x (Tkt tp') tp
hnf{TYPE} Γ u (Abs _ _ _ _ _ _) | tp'' | just (mk-abs pi Pi pi' x (Tkt tp') ff tp) = TpArrow tp' tp
hnf{TYPE} Γ u (Abs _ _ _ _ _ _) | tp'' | nothing = tp''
hnf{TYPE} Γ u (TpArrow tp1 tp2) = TpArrow (hnf Γ (unfold-dampen u) tp1) (hnf Γ (unfold-dampen u) tp2)
hnf{TYPE} Γ u (TpEq t1 t2) = TpEq (erase-term t1) (erase-term t2)
hnf{TYPE} Γ u (TpLambda pi pi' x atk tp) = 
  TpLambda pi pi' x (hnf-tk Γ (unfold-dampen u) atk) (hnf (ctxt-var-decl x Γ) (unfold-dampen u) tp)
hnf{TYPE} Γ u (Lft pi pi' y t l) = 
 let t = hnf (ctxt-var-decl y Γ) u t in
   do-lift (Lft pi pi' y t l) y l t

hnf{KIND} Γ u (KndParens _ k _) = hnf Γ u k
hnf{KIND} Γ (unfold b b') (KndVar _ x) with ctxt-lookup-kind-var-def Γ x
hnf{KIND} Γ (unfold b b') (KndVar pi x) | nothing = KndVar pi x
hnf{KIND} Γ (unfold b b') (KndVar pi x) | just k = k 
hnf{KIND} Γ no-unfolding (KndVar pi x) = KndVar pi x
hnf{KIND} Γ u (KndPi pi pi' x atk k) =
  let atk' = atk in -- hnf-tk Γ (unfold-dampen u ) atk in
  let k' = k in -- hnf Γ (unfold-dampen u) k in
    if is-free-in-kind check-erased x k then
      (KndPi pi pi' x atk' k')
    else
      tk-arrow-kind atk' k'
hnf Γ u x = x

hnf-tk Γ u (Tkk k) = Tkk (hnf Γ u k)
hnf-tk Γ u (Tkt tp) = Tkt (hnf Γ u tp)

hnf-optClass Γ u NoClass = NoClass
hnf-optClass Γ u (SomeClass atk) = SomeClass (hnf-tk Γ u atk)

conv-term-norm Γ (Var _ x) (Var _ x') = ctxt-eq-rep Γ x x'
-- hnf implements erasure for terms, so we can ignore some subterms for App and Lam cases below
conv-term-norm Γ (App t1 m t2) (App t1' m' t2') = conv-term-norm Γ t1 t1' && conv-term Γ t2 t2'
conv-term-norm Γ (Lam _ l _ x oc t) (Lam _ l' _ x' oc' t') = conv-term (ctxt-rename x x' (ctxt-var-decl x' Γ)) t t'
conv-term-norm Γ (Hole _) _ = tt
conv-term-norm Γ _ (Hole _) = tt
conv-term-norm Γ _ _ = ff

conv-type-norm Γ (TpVar _ x) (TpVar _ x') = ctxt-eq-rep Γ x x'
conv-type-norm Γ (TpApp t1 t2) (TpApp t1' t2') = conv-type-norm Γ t1 t1' && conv-type Γ t2 t2'
conv-type-norm Γ (TpAppt t1 t2) (TpAppt t1' t2') = conv-type-norm Γ t1 t1' && conv-term Γ t2 t2'
conv-type-norm Γ (Abs _ b _ x atk tp) (Abs _ b' _ x' atk' tp') = 
  eq-binder b b' && conv-tk Γ atk atk' && conv-type (ctxt-rename x x' (ctxt-var-decl x' Γ)) tp tp'
conv-type-norm Γ (TpArrow tp1 tp2) (TpArrow tp1' tp2') = conv-type Γ tp1 tp1' && conv-type Γ tp2 tp2'
conv-type-norm Γ (TpArrow tp1 tp2) (Abs _ Pi _ _ (Tkt tp1') tp2') = conv-type Γ tp1 tp1' && conv-type Γ tp2 tp2'
conv-type-norm Γ (Abs _ Pi _ _ (Tkt tp1) tp2) (TpArrow tp1' tp2') = conv-type Γ tp1 tp1' && conv-type Γ tp2 tp2'
conv-type-norm Γ (Iota _ x tp) (Iota _ x' tp') = conv-type (ctxt-rename x x' (ctxt-var-decl x' Γ)) tp tp'
conv-type-norm Γ (TpEq t1 t2) (TpEq t1' t2') = conv-term Γ t1 t1' && conv-term Γ t2 t2'
conv-type-norm Γ (Lft _ _ x t l) (Lft _ _ x' t' l') = conv-liftingType Γ l l' && conv-term (ctxt-rename x x' (ctxt-var-decl x' Γ)) t t'
conv-type-norm Γ (TpLambda _ _ x atk tp) (TpLambda _ _ x' atk' tp') =
  conv-tk Γ atk atk' && conv-type (ctxt-rename x x' (ctxt-var-decl x' Γ)) tp tp'
conv-type-norm Γ _ _ = ff 

{- even though hnf turns Pi-kinds where the variable is not free in the body into arrow kinds,
   we still need to check off-cases, because normalizing the body of a kind could cause the
   bound variable to be erased (hence allowing it to match an arrow kind). -}
conv-kind-norm Γ (KndVar _ x) (KndVar _ x') = x =string x'
conv-kind-norm Γ (KndArrow k k₁) (KndArrow k' k'') = conv-kind Γ k k' && conv-kind Γ k₁ k''
conv-kind-norm Γ (KndArrow k k₁) (KndPi _ _ x (Tkk k') k'') = conv-kind Γ k k' && conv-kind Γ k₁ k''
conv-kind-norm Γ (KndArrow k k₁) _ = ff
conv-kind-norm Γ (KndPi _ _ x (Tkk k₁) k) (KndArrow k' k'') = conv-kind Γ k₁ k' && conv-kind Γ k k''
conv-kind-norm Γ (KndPi _ _ x atk k) (KndPi _ _ x' atk' k'') = 
  let Γ' = ctxt-tk-def x x' atk Γ in
    conv-tk Γ atk atk' && conv-kind Γ' k k''
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

conv-liftingType Γ (LiftParens x l x₁) l' = conv-liftingType Γ l l'
conv-liftingType Γ l (LiftParens x l' x₁) = conv-liftingType Γ l l'
conv-liftingType Γ (LiftArrow l l1) (LiftArrow l' l1') = conv-liftingType Γ l l' && conv-liftingType Γ l1 l1'
conv-liftingType Γ (LiftPi x x₁ x₂ l) l' = ff -- unimplemented
conv-liftingType Γ (LiftStar _) (LiftStar _) = tt
conv-liftingType Γ (LiftTpArrow x l) l' = ff -- unimplemented
conv-liftingType Γ _ _ = ff

conv-optClass Γ NoClass NoClass = tt
conv-optClass Γ (SomeClass x) (SomeClass x') = conv-tk Γ x x'
conv-optClass Γ _ _ = ff

conv-tty* Γ [] [] = tt
conv-tty* Γ (tterm t :: args) (tterm t' :: args') = conv-term Γ t t' && conv-tty* Γ args args'
conv-tty* Γ (ttype t :: args) (ttype t' :: args') = conv-type Γ t t' && conv-tty* Γ args args'
conv-tty* Γ _ _ = ff
