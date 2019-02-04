module conversion where

open import lib

open import cedille-types
open import ctxt
open import is-free
open import lift
open import rename
open import subst
open import syntax-util
open import general-util
open import to-string
open import erase

{- Some notes:

   -- hnf{TERM} implements erasure as well as normalization.

   -- hnf{TYPE} does not descend into terms.

   -- definitions are assumed to be in hnf
-}

data unfolding : Set where
  no-unfolding : unfolding
  unfold : (unfold-all : 𝔹) {- if ff we unfold just the head -}
           → (unfold-lift : 𝔹) {- if tt we unfold lifting types -}
           → (dampen-after-head-beta : 𝔹) {- if tt we will not unfold definitions after a head beta reduction -}
           → (erase : 𝔹) -- if tt erase the term as we unfold
           → unfolding

unfolding-get-erased : unfolding → 𝔹
unfolding-get-erased no-unfolding = ff
unfolding-get-erased (unfold _ _ _ e) = e

unfolding-set-erased : unfolding → 𝔹 → unfolding
unfolding-set-erased no-unfolding e = no-unfolding
unfolding-set-erased (unfold b1 b2 b3 _) e = unfold b1 b2 b3 e

unfold-all : unfolding
unfold-all = unfold tt tt ff tt

unfold-head : unfolding
unfold-head = unfold ff tt ff tt

unfold-head-no-lift : unfolding
unfold-head-no-lift = unfold ff ff ff ff

unfold-head-one : unfolding
unfold-head-one = unfold ff tt tt tt

unfold-dampen : (after-head-beta : 𝔹) → unfolding → unfolding
unfold-dampen _ no-unfolding = no-unfolding
unfold-dampen _ (unfold tt b b' e) = unfold tt b b e -- we do not dampen unfolding when unfolding everywhere
unfold-dampen tt (unfold ff b tt e) = no-unfolding
unfold-dampen tt (unfold ff b ff e) = (unfold ff b ff e)
unfold-dampen ff _ = no-unfolding

unfolding-elab : unfolding → unfolding
unfolding-elab no-unfolding = no-unfolding
unfolding-elab (unfold b b' b'' _) = unfold b b' b'' ff

conv-t : Set → Set
conv-t T = ctxt → T → T → 𝔹

{-# TERMINATING #-}

-- main entry point
-- does not assume erased
conv-term : conv-t term
conv-type : conv-t type 
conv-kind : conv-t kind

-- assume erased
conv-terme : conv-t term 
conv-argse : conv-t (𝕃 term) 
conv-typee : conv-t type
conv-kinde : conv-t kind

-- call hnf, then the conv-X-norm functions
conv-term' : conv-t term 
conv-type' : conv-t type 

hnf : {ed : exprd} → ctxt → (u : unfolding) → ⟦ ed ⟧ → (is-head : 𝔹) → ⟦ ed ⟧ 

-- assume head normalized inputs
conv-term-norm : conv-t term 
conv-type-norm : conv-t type
conv-kind-norm : conv-t kind

hnf-optClass : ctxt → unfolding → optClass → optClass
-- hnf-tk : ctxt → unfolding → tk → tk

-- does not assume erased
conv-tk : conv-t tk
conv-liftingType : conv-t liftingType
conv-optClass : conv-t optClass
-- conv-optType : conv-t optType
conv-tty* : conv-t (𝕃 tty)

-- assume erased
conv-tke : conv-t tk
conv-liftingTypee : conv-t liftingType
conv-optClasse : conv-t optClass
-- -- conv-optTypee : conv-t optType
conv-ttye* : conv-t (𝕃 tty)


conv-term Γ t t' = conv-terme Γ (erase t) (erase t')

conv-terme Γ t t' with decompose-apps t | decompose-apps t'
conv-terme Γ t t' | Var _ x , args | Var _ x' , args' = 
  if ctxt-eq-rep Γ x x' && conv-argse Γ args args' then tt else
  conv-term' Γ t t'
conv-terme Γ t t' | _ | _ = conv-term' Γ t t'

conv-argse Γ [] [] = tt
conv-argse Γ (a :: args) (a' :: args') = conv-terme Γ a a' && conv-argse Γ args args'
conv-argse Γ _ _ = ff

conv-type Γ t t' = conv-typee Γ (erase t) (erase t')

conv-typee Γ t t' with decompose-tpapps t | decompose-tpapps t'
conv-typee Γ t t' | TpVar _ x , args | TpVar _ x' , args' = 
  if ctxt-eq-rep Γ x x' && conv-tty* Γ args args' then tt else
  conv-type' Γ t t'
conv-typee Γ t t' | _ | _ = conv-type' Γ t t'

conv-kind Γ k k' = conv-kinde Γ (erase k) (erase k')
conv-kinde Γ k k' = conv-kind-norm Γ (hnf Γ unfold-head k tt) (hnf Γ unfold-head k' tt)

conv-term' Γ t t' = conv-term-norm Γ (hnf Γ unfold-head t tt) (hnf Γ unfold-head t' tt)
conv-type' Γ t t' = conv-type-norm Γ (hnf Γ unfold-head t tt) (hnf Γ unfold-head t' tt)

-- is-head is only used in hnf{TYPE}
hnf{TERM} Γ no-unfolding e hd = erase-term e
hnf{TERM} Γ u (Parens _ t _) hd = hnf Γ u t hd
hnf{TERM} Γ u (App t1 Erased t2) hd = hnf Γ u t1 hd
hnf{TERM} Γ u (App t1 NotErased t2) hd with hnf Γ u t1 hd
hnf{TERM} Γ u (App _ NotErased t2) hd | Lam _ _ _ x _ t1 = hnf Γ (unfold-dampen tt u) (subst Γ t2 x t1) hd
hnf{TERM} Γ u (App _ NotErased t2) hd | t1 = App t1 NotErased (hnf Γ (unfold-dampen ff u) t2 hd)
hnf{TERM} Γ u (Lam _ Erased _ _ _ t) hd = hnf Γ u t hd
hnf{TERM} Γ u (Lam _ NotErased _ x oc t) hd with hnf (ctxt-var-decl x Γ) u t hd
hnf{TERM} Γ u (Lam _ NotErased _ x oc t) hd | (App t' NotErased (Var _ x')) with x =string x' && ~ (is-free-in skip-erased x t')
hnf{TERM} Γ u (Lam _ NotErased _ x oc t) hd | (App t' NotErased (Var _ x')) | tt = t' -- eta-contraction
hnf{TERM} Γ u (Lam _ NotErased _ x oc t) hd | (App t' NotErased (Var _ x')) | ff = 
  Lam posinfo-gen NotErased posinfo-gen x NoClass (App t' NotErased (Var posinfo-gen x'))
hnf{TERM} Γ u (Lam _ NotErased _ x oc t) hd | t' = Lam posinfo-gen NotErased posinfo-gen x NoClass t'
hnf{TERM} Γ u (Let _ (DefTerm _ x _ t) t') hd = hnf Γ u (subst Γ t x t') hd 
hnf{TERM} Γ u (Let _ (DefType _ x _ _) t') hd = hnf (ctxt-var-decl x Γ) u t' hd 
hnf{TERM} Γ (unfold _ _ _ _) (Var _ x) hd with ctxt-lookup-term-var-def Γ x
hnf{TERM} Γ (unfold _ _ _ _) (Var _ x) hd | nothing = Var posinfo-gen x
hnf{TERM} Γ (unfold ff _ _ e) (Var _ x) hd | just t = erase-if e t -- definitions should be stored in hnf
hnf{TERM} Γ (unfold tt b b' e) (Var _ x) hd | just t = hnf Γ (unfold tt b b' e) t hd -- this might not be fully normalized, only head-normalized
hnf{TERM} Γ u (AppTp t tp) hd = hnf Γ u t hd
hnf{TERM} Γ u (Sigma _ t) hd = hnf Γ u t hd
hnf{TERM} Γ u (Epsilon _ _ _ t) hd = hnf Γ u t hd
hnf{TERM} Γ u (IotaPair _ t1 t2 _ _) hd = hnf Γ u t1 hd
hnf{TERM} Γ u (IotaProj t _ _) hd = hnf Γ u t hd
hnf{TERM} Γ u (Phi _ eq t₁ t₂ _) hd = hnf Γ u t₂ hd
hnf{TERM} Γ u (Rho _ _ _ t _ t') hd = hnf Γ u t' hd
hnf{TERM} Γ u (Chi _ T t') hd = hnf Γ u t' hd
hnf{TERM} Γ u (Delta _ T t') hd = hnf Γ u t' hd
hnf{TERM} Γ u (Theta _ u' t ls) hd = hnf Γ u (lterms-to-term u' t ls) hd
hnf{TERM} Γ u (Beta _ _ (SomeTerm t _)) hd = hnf Γ u t hd
hnf{TERM} Γ u (Beta _ _ NoTerm) hd = id-term
hnf{TERM} Γ u (Open _ _ t) hd = hnf Γ u t hd
hnf{TERM} Γ u x hd = x

hnf{TYPE} Γ no-unfolding e _ = e
hnf{TYPE} Γ u (TpParens _ t _) hd = hnf Γ u t hd
hnf{TYPE} Γ u (NoSpans t _)  hd = hnf Γ u t hd
hnf{TYPE} Γ (unfold b b' _ _) (TpVar _ x) ff  = TpVar posinfo-gen x 
hnf{TYPE} Γ (unfold b b' _ _) (TpVar _ x) tt with ctxt-lookup-type-var-def Γ x
hnf{TYPE} Γ (unfold b b' _ _) (TpVar _ x) tt | just tp = tp
hnf{TYPE} Γ (unfold b b' _ _) (TpVar _ x) tt | nothing = TpVar posinfo-gen x
hnf{TYPE} Γ u (TpAppt tp t) hd with hnf Γ u tp hd
hnf{TYPE} Γ u (TpAppt _ t) hd  | TpLambda _ _ x _ tp = hnf Γ u (subst Γ t x tp) hd
hnf{TYPE} Γ u (TpAppt _ t) hd | tp = TpAppt tp (erase-if (unfolding-get-erased u) t)
hnf{TYPE} Γ u (TpApp tp tp') hd with hnf Γ u tp hd
hnf{TYPE} Γ u (TpApp _ tp') hd | TpLambda _ _ x _ tp = hnf Γ u (subst Γ tp' x tp) hd 
hnf{TYPE} Γ u (TpApp _ tp') hd | tp with hnf Γ u tp' hd 
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
                try-pull-term-in Γ (Lam _ _ _ x _ t) (LiftArrow l1 l2) (suc n) vars ltps =
                  try-pull-term-in (ctxt-var-decl x Γ) t l2 n (x :: vars) (l1 :: ltps) 
                try-pull-term-in Γ t (LiftArrow l1 l2) (suc n) vars ltps =
                  let x = fresh-var "x" (ctxt-binds-var Γ) empty-renamectxt in
                    try-pull-term-in (ctxt-var-decl x Γ) (App t NotErased (mvar x)) l2 n (x :: vars) (l1 :: ltps) 
                try-pull-term-in Γ t l n vars ltps = TpApp tp1 tp2

        try-pull-lift-types tp1 tp2 | _ | _ = TpApp tp1 tp2


hnf{TYPE} Γ u (Abs _ b _ x atk tp) _ with Abs posinfo-gen b posinfo-gen x atk (hnf (ctxt-var-decl x Γ) u tp ff)
hnf{TYPE} Γ u (Abs _ b _ x atk tp) _ | tp' with to-abs tp'
hnf{TYPE} Γ u (Abs _ _ _ _ _ _) _ | tp'' | just (mk-abs b x atk tt {- x is free in tp -} tp) = Abs posinfo-gen b posinfo-gen x atk tp
hnf{TYPE} Γ u (Abs _ _ _ _ _ _) _ | tp'' | just (mk-abs b x (Tkk k) ff tp) = Abs posinfo-gen b posinfo-gen x (Tkk k) tp
hnf{TYPE} Γ u (Abs _ _ _ _ _ _) _ | tp'' | just (mk-abs b x (Tkt tp') ff tp) = TpArrow tp' b tp
hnf{TYPE} Γ u (Abs _ _ _ _ _ _) _ | tp'' | nothing = tp''
hnf{TYPE} Γ u (TpArrow tp1 arrowtype tp2) _ = TpArrow (hnf Γ u tp1 ff) arrowtype (hnf Γ u tp2 ff)
hnf{TYPE} Γ u (TpEq _ t1 t2 _) _
  = TpEq posinfo-gen (erase t1) (erase t2) posinfo-gen
hnf{TYPE} Γ u (TpLambda _ _ x atk tp) _ = 
  TpLambda posinfo-gen posinfo-gen x (hnf Γ u atk ff) (hnf (ctxt-var-decl x Γ) u tp ff)
hnf{TYPE} Γ u @ (unfold b tt b'' b''') (Lft _ _ y t l) _ = 
 let t = hnf (ctxt-var-decl y Γ) u t tt in
   do-lift Γ (Lft posinfo-gen posinfo-gen y t l) y l (λ t → hnf{TERM} Γ unfold-head t ff) t
-- We need hnf{TYPE} to preserve types' well-kindedness, so we must check if
-- the defined term is being checked against a type and use chi to make sure
-- that wherever it is substituted, the term will have the same directionality.
-- For example, "[e ◂ {a ≃ b} = ρ e' - β] - A (ρ e - a)", would otherwise
-- head-normalize to A (ρ (ρ e' - β) - a), which wouldn't check because it
-- synthesizes the type of "ρ e' - β" (which in turn fails to synthesize the type
-- of "β"). Similar issues could happen if the term is synthesized and it uses a ρ,
-- and then substitutes into a place where it would be checked against a type.
hnf{TYPE} Γ u (TpLet _ (DefTerm _ x ot t) T) hd =
  hnf Γ u (subst Γ (Chi posinfo-gen ot t) x T) hd
-- Note that if we ever remove the requirement that type-lambdas have a classifier,
-- we would need to introduce a type-level chi to do the same thing as above.
-- Currently, synthesizing or checking a type should not make a difference.
hnf{TYPE} Γ u (TpLet _ (DefType _ x k T) T') hd = hnf Γ u (subst Γ T x T') hd
hnf{TYPE} Γ u x _ = x

hnf{KIND} Γ no-unfolding e hd = e
hnf{KIND} Γ u (KndParens _ k _) hd = hnf Γ u k hd
hnf{KIND} Γ (unfold _ _ _ _) (KndVar _ x ys) _ with ctxt-lookup-kind-var-def Γ x 
... | nothing = KndVar posinfo-gen x ys
... | just (ps , k) = fst $ subst-params-args Γ ps ys k {- do-subst ys ps k
  where do-subst : args → params → kind → kind
        do-subst (ArgsCons (TermArg _ t) ys) (ParamsCons (Decl _ _ _ x _ _) ps) k = do-subst ys ps (subst Γ t x k)
        do-subst (ArgsCons (TypeArg t) ys) (ParamsCons (Decl _ _ _ x _ _) ps) k = do-subst ys ps (subst Γ t x k)
        do-subst _ _ k = k -- should not happen -}

hnf{KIND} Γ u (KndPi _ _ x atk k) hd =
    if is-free-in check-erased x k then
      (KndPi posinfo-gen posinfo-gen x atk k)
    else
      tk-arrow-kind atk k
hnf{KIND} Γ u x hd = x

hnf{LIFTINGTYPE} Γ u x hd = x
hnf{TK} Γ u (Tkk k) _ = Tkk (hnf Γ u k tt)
hnf{TK} Γ u (Tkt tp) _ = Tkt (hnf Γ u tp ff)
hnf{QUALIF} Γ u x hd = x
hnf{ARG} Γ u x hd = x

hnf-optClass Γ u NoClass = NoClass
hnf-optClass Γ u (SomeClass atk) = SomeClass (hnf Γ u atk ff)

{- this function reduces a term to "head-applicative" normal form,
   which avoids unfolding definitions if they would lead to a top-level
   lambda-abstraction or top-level application headed by a variable for which we
   do not have a (global) definition. -}
{-# TERMINATING #-}
hanf : ctxt → (e : 𝔹) → term → term
hanf Γ e t with hnf Γ (unfolding-set-erased unfold-head-one e) t tt
hanf Γ e t | t' with decompose-apps t'
hanf Γ e t | t' | (Var _ x) , [] = t'
hanf Γ e t | t' | (Var _ x) , args with ctxt-lookup-term-var-def Γ x 
hanf Γ e t | t' | (Var _ x) , args | nothing = t'
hanf Γ e t | t' | (Var _ x) , args | just _ = hanf Γ e t'
hanf Γ e t | t' | h , args {- h could be a Lambda if args is [] -} = t

-- unfold across the term-type barrier
hnf-term-type : ctxt → (e : 𝔹) → type → type
hnf-term-type Γ e (TpEq _ t1 t2 _) = TpEq posinfo-gen (hanf Γ e t1) (hanf Γ e t2) posinfo-gen
hnf-term-type Γ e (TpAppt tp t) = hnf Γ (unfolding-set-erased unfold-head e) (TpAppt tp (hanf Γ e t)) tt
hnf-term-type Γ e tp = hnf Γ unfold-head tp tt

conv-term-norm Γ (Var _ x) (Var _ x') = ctxt-eq-rep Γ x x'
-- hnf implements erasure for terms, so we can ignore some subterms for App and Lam cases below
conv-term-norm Γ (App t1 m t2) (App t1' m' t2') = conv-term-norm Γ t1 t1' && conv-term Γ t2 t2'
conv-term-norm Γ (Lam _ l _ x oc t) (Lam _ l' _ x' oc' t') = conv-term (ctxt-rename x x' (ctxt-var-decl-if x' Γ)) t t'
conv-term-norm Γ (Hole _) _ = tt
conv-term-norm Γ _ (Hole _) = tt
-- conv-term-norm Γ (Beta _ _ NoTerm) (Beta _ _ NoTerm) = tt
-- conv-term-norm Γ (Beta _ _ (SomeTerm t _)) (Beta _ _ (SomeTerm t' _)) = conv-term Γ t t'
-- conv-term-norm Γ (Beta _ _ _) (Beta _ _ _) = ff
{- it can happen that a term is equal to a lambda abstraction in head-normal form,
   if that lambda-abstraction would eta-contract following some further beta-reductions.
   We implement this here by implicitly eta-expanding the variable and continuing
   the comparison.

   A simple example is 

       λ v . t ((λ a . a) v) ≃ t
 -}
conv-term-norm Γ (Lam _ l _ x oc t) t' =
  let x' = fresh-var x (ctxt-binds-var Γ) empty-renamectxt in
  conv-term (ctxt-rename x x' Γ) t (App t' NotErased (Var posinfo-gen x'))
conv-term-norm Γ t' (Lam _ l _ x oc t) =
  let x' = fresh-var x (ctxt-binds-var Γ) empty-renamectxt in
  conv-term (ctxt-rename x x' Γ) (App t' NotErased (Var posinfo-gen x')) t 
conv-term-norm Γ _ _ = ff

conv-type-norm Γ (TpVar _ x) (TpVar _ x') = ctxt-eq-rep Γ x x'
conv-type-norm Γ (TpApp t1 t2) (TpApp t1' t2') = conv-type-norm Γ t1 t1' && conv-type Γ t2 t2'
conv-type-norm Γ (TpAppt t1 t2) (TpAppt t1' t2') = conv-type-norm Γ t1 t1' && conv-term Γ t2 t2'
conv-type-norm Γ (Abs _ b _ x atk tp) (Abs _ b' _ x' atk' tp') = 
  eq-maybeErased b b' && conv-tk Γ atk atk' && conv-type (ctxt-rename x x' (ctxt-var-decl-if x' Γ)) tp tp'
conv-type-norm Γ (TpArrow tp1 a1 tp2) (TpArrow tp1' a2  tp2') = eq-maybeErased a1 a2 && conv-type Γ tp1 tp1' && conv-type Γ tp2 tp2'
conv-type-norm Γ (TpArrow tp1 a tp2) (Abs _ b _ _ (Tkt tp1') tp2') = eq-maybeErased a b && conv-type Γ tp1 tp1' && conv-type Γ tp2 tp2'
conv-type-norm Γ (Abs _ b _ _ (Tkt tp1) tp2) (TpArrow tp1' a tp2') = eq-maybeErased a b && conv-type Γ tp1 tp1' && conv-type Γ tp2 tp2'
conv-type-norm Γ (Iota _ _ x m tp) (Iota _ _ x' m' tp') = 
  conv-type Γ m m' && conv-type (ctxt-rename x x' (ctxt-var-decl-if x' Γ)) tp tp'
conv-type-norm Γ (TpEq _ t1 t2 _) (TpEq _ t1' t2' _) = conv-term Γ t1 t1' && conv-term Γ t2 t2'
conv-type-norm Γ (Lft _ _ x t l) (Lft _ _ x' t' l') =
  conv-liftingType Γ l l' && conv-term (ctxt-rename x x' (ctxt-var-decl-if x' Γ)) t t'
conv-type-norm Γ (TpLambda _ _ x atk tp) (TpLambda _ _ x' atk' tp') =
  conv-tk Γ atk atk' && conv-type (ctxt-rename x x' (ctxt-var-decl-if x' Γ)) tp tp'
conv-type-norm Γ _ _ = ff 

{- even though hnf turns Pi-kinds where the variable is not free in the body into arrow kinds,
   we still need to check off-cases, because normalizing the body of a kind could cause the
   bound variable to be erased (hence allowing it to match an arrow kind). -}
conv-kind-norm Γ (KndArrow k k₁) (KndArrow k' k'') = conv-kind Γ k k' && conv-kind Γ k₁ k''
conv-kind-norm Γ (KndArrow k k₁) (KndPi _ _ x (Tkk k') k'') = conv-kind Γ k k' && conv-kind Γ k₁ k''
conv-kind-norm Γ (KndArrow k k₁) _ = ff
conv-kind-norm Γ (KndPi _ _ x (Tkk k₁) k) (KndArrow k' k'') = conv-kind Γ k₁ k' && conv-kind Γ k k''
conv-kind-norm Γ (KndPi _ _ x atk k) (KndPi _ _ x' atk' k'') = 
    conv-tk Γ atk atk' && conv-kind (ctxt-rename x x' (ctxt-var-decl-if x' Γ)) k k''
conv-kind-norm Γ (KndPi _ _ x (Tkt t) k) (KndTpArrow t' k'') = conv-type Γ t t' && conv-kind Γ k k''
conv-kind-norm Γ (KndPi _ _ x (Tkt t) k) _ = ff
conv-kind-norm Γ (KndPi _ _ x (Tkk k') k) _ = ff
conv-kind-norm Γ (KndTpArrow t k) (KndTpArrow t' k') = conv-type Γ t t' && conv-kind Γ k k'
conv-kind-norm Γ (KndTpArrow t k) (KndPi _ _ x (Tkt t') k') = conv-type Γ t t' && conv-kind Γ k k'
conv-kind-norm Γ (KndTpArrow t k) _ = ff
conv-kind-norm Γ (Star x) (Star x') = tt
conv-kind-norm Γ (Star x) _ = ff
conv-kind-norm Γ _ _ = ff -- should not happen, since the kinds are in hnf

conv-tk Γ tk tk' = conv-tke Γ (erase-tk tk) (erase-tk tk')

conv-tke Γ (Tkk k) (Tkk k') = conv-kind Γ k k'
conv-tke Γ (Tkt t) (Tkt t') = conv-type Γ t t'
conv-tke Γ _ _ = ff

conv-liftingType Γ l l' = conv-liftingTypee Γ (erase l) (erase l')
conv-liftingTypee Γ l l' = conv-kind Γ (liftingType-to-kind l) (liftingType-to-kind l')

conv-optClass Γ NoClass NoClass = tt
conv-optClass Γ (SomeClass x) (SomeClass x') = conv-tk Γ (erase-tk x) (erase-tk x')
conv-optClass Γ _ _ = ff

conv-optClasse Γ NoClass NoClass = tt
conv-optClasse Γ (SomeClass x) (SomeClass x') = conv-tk Γ x x'
conv-optClasse Γ _ _ = ff

-- conv-optType Γ NoType NoType = tt
-- conv-optType Γ (SomeType x) (SomeType x') = conv-type Γ x x'
-- conv-optType Γ _ _ = ff

conv-tty* Γ [] [] = tt
conv-tty* Γ (tterm t :: args) (tterm t' :: args')
  = conv-term Γ (erase t) (erase t') && conv-tty* Γ args args'
conv-tty* Γ (ttype t :: args) (ttype t' :: args')
  = conv-type Γ (erase t) (erase t') && conv-tty* Γ args args'
conv-tty* Γ _ _ = ff

conv-ttye* Γ [] [] = tt
conv-ttye* Γ (tterm t :: args) (tterm t' :: args') = conv-term Γ t t' && conv-ttye* Γ args args'
conv-ttye* Γ (ttype t :: args) (ttype t' :: args') = conv-type Γ t t' && conv-ttye* Γ args args'
conv-ttye* Γ _ _ = ff

hnf-qualif-term : ctxt → term → term
hnf-qualif-term Γ t = hnf Γ unfold-head (qualif-term Γ t) tt

hnf-qualif-type : ctxt → type → type
hnf-qualif-type Γ t = hnf Γ unfold-head (qualif-type Γ t) tt

hnf-qualif-kind : ctxt → kind → kind
hnf-qualif-kind Γ t = hnf Γ unfold-head (qualif-kind Γ t) tt

ctxt-params-def : params → ctxt → ctxt
ctxt-params-def ps Γ@(mk-ctxt (fn , mn , _ , q) syms i symb-occs d) =
  mk-ctxt (fn , mn , ps' , q) syms i symb-occs d
  where ps' = qualif-params Γ ps

ctxt-kind-def : posinfo → var → params → kind → ctxt → ctxt
ctxt-kind-def pi v ps2 k Γ@(mk-ctxt (fn , mn , ps1 , q) (syms , mn-fn) i symb-occs d) = mk-ctxt
  (fn , mn , ps1 , qualif-insert-params q (mn # v) v ps1)
  (trie-insert-append2 syms fn mn v , mn-fn)
  (trie-insert i (mn # v) (kind-def (append-params ps1 $ qualif-params Γ ps2) k' , fn , pi))
  symb-occs
  d
  where
  k' = hnf Γ unfold-head (qualif-kind Γ k) tt

-- assumption: classifier (i.e. kind) already qualified
ctxt-datatype-def : posinfo → var → params → kind → defDatatype → ctxt → ctxt
ctxt-datatype-def pi v pa k dd Γ@(mk-ctxt (fn , mn , ps , q) (syms , mn-fn) i symb-occs d) = mk-ctxt
  (fn , mn , ps , q') 
  ((trie-insert-append2 syms fn mn v) , mn-fn)
  (trie-insert i v' (datatype-def pa k , fn , pi))
  symb-occs
  (trie-insert d v' dd)
  where
  v' = mn # v
  q' = qualif-insert-params q v' v ps

-- assumption: classifier (i.e. kind) already qualified
ctxt-type-def : posinfo → defScope → opacity → var → type → kind → ctxt → ctxt
ctxt-type-def pi s op v t k Γ@(mk-ctxt (fn , mn , ps , q) (syms , mn-fn) i symb-occs d) = mk-ctxt
  (fn , mn , ps , q')
  ((if (s iff localScope) then syms else trie-insert-append2 syms fn mn v) , mn-fn)
  (trie-insert i v' (type-def (def-params s ps) op t' k , fn , pi))
  symb-occs
  d
  where
  t' = hnf Γ unfold-head (qualif-type Γ t) tt
  v' = if s iff localScope then pi % v else mn # v
  q' = qualif-insert-params q v' v ps

ctxt-const-def : posinfo → var → type → ctxt → ctxt
ctxt-const-def pi c t Γ@(mk-ctxt mod@(fn , mn , ps , q) (syms , mn-fn) i symb-occs d) = mk-ctxt
  (fn , mn , ps , q')
  ((trie-insert-append2 syms fn mn c) , mn-fn)  
  (trie-insert i c' (const-def t , fn , pi))
  symb-occs
  d
  where
  c' = mn # c
  q' = qualif-insert-params q c' c ps

-- assumption: classifier (i.e. type) already qualified
ctxt-term-def : posinfo → defScope → opacity → var → term → type → ctxt → ctxt
ctxt-term-def pi s op v t tp Γ@(mk-ctxt (fn , mn , ps , q) (syms , mn-fn) i symb-occs d) = mk-ctxt
  (fn , mn , ps , q')
  ((if (s iff localScope) then syms else trie-insert-append2 syms fn mn v) , mn-fn)
  (trie-insert i v' (term-def (def-params s ps) op t' tp , fn , pi))
  symb-occs
  d
  where
  t' = hnf Γ unfold-head (qualif-term Γ t) tt
  v' = if s iff localScope then pi % v else mn # v
  q' = qualif-insert-params q v' v ps

ctxt-term-udef : posinfo → defScope → opacity → var → term → ctxt → ctxt
ctxt-term-udef pi s op v t Γ@(mk-ctxt (fn , mn , ps , q) (syms , mn-fn) i symb-occs d) = mk-ctxt
  (fn , mn , ps , qualif-insert-params q v' v ps)
  ((if (s iff localScope) then syms else trie-insert-append2 syms fn mn v) , mn-fn)
  (trie-insert i v' (term-udef (def-params s ps) op t' , fn , pi))
  symb-occs
  d
  where
  t' = hnf Γ unfold-head (qualif-term Γ t) tt
  v' = if s iff localScope then pi % v else mn # v
