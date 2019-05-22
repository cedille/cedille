module conversion where

open import lib

open import constants
open import cedille-types
open import ctxt
open import free-vars
open import rename
open import subst
open import syntax-util
open import general-util
open import type-util

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

--hnf-optClass : ctxt → unfolding → optClass → optClass
-- hnf-tpkd : ctxt → unfolding → tpkd → tpkd

-- does not assume erased
conv-tpkd : conv-t tpkd
--conv-liftingType : conv-t liftingType
--conv-optClass : conv-t optClass
-- conv-optType : conv-t optType
conv-tty* : conv-t (𝕃 tty)

-- assume erased
conv-tpkde : conv-t tpkd
--conv-liftingTypee : conv-t liftingType
--conv-optClasse : conv-t optClass
-- -- conv-optTypee : conv-t optType
conv-ttye* : conv-t (𝕃 tty)

conv-ctr-ps : ctxt → var → var → maybe (ℕ × ℕ)
conv-ctr-args : conv-t (var × args)
conv-ctr : conv-t var

conv-term Γ t t' = conv-terme Γ (erase t) (erase t')

conv-terme Γ t t' with decompose-apps t | decompose-apps t'
conv-terme Γ t t' | Var x , args | Var x' , args' = 
     ctxt-eq-rep Γ x x' && conv-argse Γ (erase-args args) (erase-args args')
  || conv-ctr-args Γ (x , args) (x' , args')
  || conv-term' Γ t t'
conv-terme Γ t t' | _ | _ = conv-term' Γ t t'

conv-argse Γ [] [] = tt
conv-argse Γ (a :: args) (a' :: args') = conv-terme Γ a a' && conv-argse Γ args args'
conv-argse Γ _ _ = ff

conv-type Γ t t' = conv-typee Γ (erase t) (erase t')

conv-typee Γ t t' with decompose-tpapps t | decompose-tpapps t'
conv-typee Γ t t' | TpVar x , args | TpVar x' , args' = 
     ctxt-eq-rep Γ x x' && conv-tty* Γ args args'
  || conv-type' Γ t t'
conv-typee Γ t t' | _ | _ = conv-type' Γ t t'

conv-kind Γ k k' = conv-kinde Γ (erase k) (erase k')
conv-kinde Γ k k' = conv-kind-norm Γ (hnf Γ unfold-head k tt) (hnf Γ unfold-head k' tt)

conv-term' Γ t t' = conv-term-norm Γ (hnf Γ unfold-head t tt) (hnf Γ unfold-head t' tt)
conv-type' Γ t t' = conv-type-norm Γ (hnf Γ unfold-head t tt) (hnf Γ unfold-head t' tt)

-- is-head is only used in hnf{TYPE}
hnf{TERM} Γ no-unfolding e hd = erase e
--hnf{TERM} Γ u (Parens _ t _) hd = hnf Γ u t hd
hnf{TERM} Γ u (App t1 tt t2) hd = hnf Γ u t1 hd
hnf{TERM} Γ u (App t1 ff t2) hd with hnf Γ u t1 hd
hnf{TERM} Γ u (App _ ff t2) hd | Lam ff x _ t1 = hnf Γ (unfold-dampen tt u) (subst Γ t2 x t1) hd
hnf{TERM} Γ u (App _ ff t2) hd | t1 = App t1 ff (hnf Γ (unfold-dampen ff u) t2 ff)
hnf{TERM} Γ u (Lam tt _ _ t) hd = hnf Γ u t hd
hnf{TERM} Γ u (Lam ff x _ t) hd with hnf (ctxt-var-decl x Γ) u t hd
hnf{TERM} Γ u (Lam ff x _ t) hd | (App t' ff (Var x')) with x =string x' && ~ (is-free-in x (erase t'))
hnf{TERM} Γ u (Lam ff x _ t) hd | (App t' ff (Var x')) | tt = t' -- eta-contraction
hnf{TERM} Γ u (Lam ff x _ t) hd | (App t' ff (Var x')) | ff = 
  Lam ff x nothing (App t' ff (Var x'))
hnf{TERM} Γ u (Lam ff x _ t) hd | t' = Lam ff x nothing t'
hnf{TERM} Γ u (LetTm ff x _ t t') hd = hnf Γ u (subst Γ t x t') hd
hnf{TERM} Γ u (LetTm tt x _ t t') hd = hnf Γ u t' hd 
hnf{TERM} Γ u (LetTp x k T t') hd = hnf Γ u t' hd 
hnf{TERM} Γ (unfold _ _ _ _) (Var x) hd with ctxt-lookup-term-var-def Γ x
hnf{TERM} Γ (unfold _ _ _ _) (Var x) hd | nothing = Var x
hnf{TERM} Γ (unfold ff _ _ e) (Var x) hd | just t = erase-if e t -- definitions should be stored in hnf
hnf{TERM} Γ (unfold tt b b' e) (Var x) hd | just t = hnf Γ (unfold tt b b' e) t hd -- this might not be fully normalized, only head-normalized
hnf{TERM} Γ u (AppTp t tp) hd = hnf Γ u t hd
hnf{TERM} Γ u (Sigma t) hd = hnf Γ u t hd
hnf{TERM} Γ u (IotaPair t1 t2 x T) hd = hnf Γ u t1 hd
hnf{TERM} Γ u (IotaProj t _) hd = hnf Γ u t hd
hnf{TERM} Γ u (Phi tₑ t₁ t₂) hd = hnf Γ u t₂ hd
hnf{TERM} Γ u (Rho _ _ _ t) hd = hnf Γ u t hd
hnf{TERM} Γ u (Delta _ _) hd = id-term
hnf{TERM} Γ u (Beta _ (just t)) hd = hnf Γ u t hd
hnf{TERM} Γ u (Beta _ nothing) hd = id-term
hnf{TERM} Γ u (Open _ _ t) hd = hnf Γ u t hd
hnf{TERM} Γ u (Mu (inj₁ _) t _ _ cs) hd with decompose-apps (hnf Γ u t hd)
hnf{TERM} Γ u (Mu (inj₁ _) t _ t~ cs) hd | tₕ , as with Mu (inj₁ nothing) (recompose-apps as tₕ) nothing (hnf Γ u t~ hd) (map (λ {(Case x as' t) → Case x as' (hnf (foldr (λ {(CaseArg _ x) → ctxt-var-decl x}) Γ as') (unfold-dampen ff u) t hd)}) (erase-cases cs)) | tₕ
hnf{TERM} Γ u (Mu (inj₁ _) t _ _ cs) hd | _ , as |  tₒ | Var x with foldl (λ {(Case xₘ cas tₘ) m? → m? maybe-or (conv-ctr-ps Γ xₘ x ≫=maybe uncurry λ psₘ ps → just (case-args-to-lams cas tₘ , length (erase-case-args cas) , ps))}) nothing (erase-cases cs)
hnf{TERM} Γ u (Mu (inj₁ _) t _ _ cs) hd | _ , as | tₒ | Var x | just (tₓ , nas , nps) with drop nps (erase-args as)
hnf{TERM} Γ u (Mu (inj₁ _) t _ _ cs) hd | _ , as | tₒ | Var x | just (tₓ , nas , nps) | as' with nas =ℕ length as'
hnf{TERM} Γ u (Mu (inj₁ _) t _ _ cs) hd | _ , as | tₒ | Var x | just (tₓ , nas , nps) | as' | tt = hnf Γ (unfold-dampen tt u) (recompose-apps (map (TmArg ff) as') tₓ) hd
hnf{TERM} Γ u (Mu (inj₁ _) t _ _ cs) hd | _ , as | tₒ | Var x | just (tₓ , nas , nps) | as' | ff = tₒ
hnf{TERM} Γ u (Mu (inj₁ _) t _ _ cs) hd | _ , as | tₒ | Var x | nothing = tₒ
hnf{TERM} Γ u (Mu (inj₁ _) t _ _ cs) hd | _ , as | tₒ | _ = tₒ
hnf{TERM} Γ u (Mu (inj₂ x) t _ _ cs) hd with decompose-apps (hnf Γ u t hd)
hnf{TERM} Γ u (Mu (inj₂ x) t _ t~ cs) hd | tₕ , as with (λ t → Mu (inj₂ x) t nothing (hnf Γ u t~ hd) (map (λ {(Case x as' t) → Case x as' (hnf (foldr (λ {(CaseArg e x) → ctxt-var-decl x}) Γ as') (unfold-dampen ff u) t hd)}) (erase-cases cs))) | tₕ
hnf{TERM} Γ u (Mu (inj₂ x) t _ _ cs) hd | tₕ , as | tₒ | Var x' with foldl (λ {(Case xₘ cas tₘ) m? → m? maybe-or (conv-ctr-ps Γ xₘ x' ≫=maybe uncurry λ psₘ ps → just (case-args-to-lams cas tₘ , length (erase-case-args cas) , ps))}) nothing (erase-cases cs) | fresh-var Γ "x"
hnf{TERM} Γ u (Mu (inj₂ x) t _ _ cs) hd | tₕ , as | tₒ | Var x' | just (tₓ , nas , nps) | fₓ with drop nps (erase-args as)
hnf{TERM} Γ u (Mu (inj₂ x) t _ _ cs) hd | tₕ , as | tₒ | Var x' | just (tₓ , nas , nps) | fₓ | as' with nas =ℕ length as'
hnf{TERM} Γ u (Mu (inj₂ x) t _ _ cs) hd | tₕ , as | tₒ | Var x' | just (tₓ , nas , nps) | fₓ | as' | tt = hnf Γ (unfold-dampen tt u) (recompose-apps (map (TmArg ff) as') (subst Γ (mlam fₓ $ tₒ $ Var fₓ) x tₓ)) hd
hnf{TERM} Γ u (Mu (inj₂ x) t _ _ cs) hd | tₕ , as | tₒ | Var x' | just (tₓ , nas , nps) | fₓ | as' | ff = tₒ $ recompose-apps (map (TmArg ff) as') tₕ
hnf{TERM} Γ u (Mu (inj₂ x) t _ _ cs) hd | tₕ , as | tₒ | Var x' | nothing | fₓ = tₒ $ recompose-apps as tₕ
hnf{TERM} Γ u (Mu (inj₂ x) t _ _ cs) hd | tₕ , as | tₒ | _ = tₒ $ recompose-apps as tₕ
hnf{TERM} Γ u x hd = x

hnf{TYPE} Γ no-unfolding e _ = e
hnf{TYPE} Γ u@(unfold ff b' _ _) (TpVar x) ff  = TpVar x 
hnf{TYPE} Γ u@(unfold b b' _ _) (TpVar x) hd with ctxt-lookup-type-var-def Γ x
hnf{TYPE} Γ u@(unfold b b' _ _) (TpVar x) hd | just tp = if b then hnf Γ u tp hd else tp
hnf{TYPE} Γ u@(unfold b b' _ _) (TpVar x) hd | nothing = TpVar x
hnf{TYPE} Γ u (TpAppt tp t) hd with hnf Γ u tp hd
hnf{TYPE} Γ u (TpAppt _ t) hd  | TpLam x _ tp = hnf Γ u (subst Γ t x tp) hd
hnf{TYPE} Γ u (TpAppt _ t) hd | tp = TpAppt tp (erase-if (unfolding-get-erased u) t)
hnf{TYPE} Γ u (TpApp tp tp') hd with hnf Γ u tp hd
hnf{TYPE} Γ u (TpApp _ tp') hd | TpLam x _ tp = hnf Γ u (subst Γ tp' x tp) hd 
hnf{TYPE} Γ u (TpApp _ tp') hd | tp with hnf Γ u tp' hd 
hnf{TYPE} Γ u (TpApp _ _) hd | tp | tp' = TpApp tp tp'
hnf{TYPE} Γ u@(unfold all? _ _ _) (TpAbs me x atk tp) _ =
  TpAbs me x (hnf Γ u atk ff) (hnf (ctxt-var-decl x Γ) u tp ff)
hnf{TYPE} Γ u (TpEq t₁ t₂) _
  = TpEq (erase t₁) (erase t₂)
hnf{TYPE} Γ u (TpLam x atk tp) _ = 
  TpLam x (hnf Γ u atk ff) (hnf (ctxt-var-decl x Γ) u tp ff)
hnf{TYPE} Γ u@(unfold tt _ _ _) (TpIota x T₁ T₂) hd = TpIota x (hnf Γ u T₁ ff) (hnf Γ u T₂ ff)
hnf{TYPE} Γ u x _ = x

hnf{KIND} Γ no-unfolding e hd = e
hnf{KIND} Γ u@(unfold a _ _ _) (KdAbs x atk k) hd =
  KdAbs x atk (if a then hnf (ctxt-var-decl x Γ) u k ff else k)
hnf{KIND} Γ u KdStar hd = KdStar

hnf{TPKD} Γ u (Tkk k) _ = Tkk (hnf Γ u k tt)
hnf{TPKD} Γ u (Tkt tp) _ = Tkt (hnf Γ u tp ff)

{- this function reduces a term to "head-applicative" normal form,
   which avoids unfolding definitions if they would lead to a top-level
   lambda-abstraction or top-level application headed by a variable for which we
   do not have a (global) definition. -}
{-# TERMINATING #-}
hanf : ctxt → (e : 𝔹) → term → term
hanf Γ e t with hnf Γ (unfolding-set-erased unfold-head-one e) t tt
hanf Γ e t | t' with decompose-apps t'
hanf Γ e t | t' | (Var x) , [] = t'
hanf Γ e t | t' | (Var x) , args with ctxt-lookup-term-var-def Γ x 
hanf Γ e t | t' | (Var x) , args | nothing = t'
hanf Γ e t | t' | (Var x) , args | just _ = hanf Γ e t'
hanf Γ e t | t' | h , args {- h could be a Lambda if args is [] -} = t

-- unfold across the term-type barrier
hnf-term-type : ctxt → (e : 𝔹) → type → type
hnf-term-type Γ e (TpEq t₁ t₂) = TpEq (hanf Γ e t₁) (hanf Γ e t₂)
hnf-term-type Γ e (TpAppt tp t) = hnf Γ (unfolding-set-erased unfold-head e) (TpAppt tp (hanf Γ e t)) tt
hnf-term-type Γ e tp = hnf Γ unfold-head tp tt


conv-cases : conv-t cases
conv-cases Γ cs₁ cs₂ = isJust $ foldl (λ c₂ x → x ≫=maybe λ cs₁ → conv-cases' Γ cs₁ c₂) (just cs₁) cs₂ where
  conv-cases' : ctxt → cases → case → maybe cases
  conv-cases' Γ [] (Case x₂ as₂ t₂) = nothing
  conv-cases' Γ (c₁ @ (Case x₁ as₁ t₁) :: cs₁) c₂ @ (Case x₂ as₂ t₂) with conv-ctr Γ x₁ x₂
  ...| ff = conv-cases' Γ cs₁ c₂ ≫=maybe λ cs₁ → just (c₁ :: cs₁)
  ...| tt = maybe-if (length as₂ =ℕ length as₁ && conv-term Γ (expand-case c₁) (expand-case (Case x₂ as₂ t₂))) ≫maybe just cs₁

ctxt-term-udef : posinfo → defScope → opacity → var → term → ctxt → ctxt

conv-term-norm Γ (Var x) (Var x') = ctxt-eq-rep Γ x x' || conv-ctr Γ x x'
-- hnf implements erasure for terms, so we can ignore some subterms for App and Lam cases below
conv-term-norm Γ (App t1 ff t2) (App t1' ff t2') = conv-term-norm Γ t1 t1' && conv-term Γ t2 t2'
conv-term-norm Γ (Lam ff x _ t) (Lam ff x' _ t') = conv-term (ctxt-rename x x' (ctxt-var-decl-if x' Γ)) t t'
conv-term-norm Γ (Hole _) _ = tt
conv-term-norm Γ _ (Hole _) = tt
conv-term-norm Γ (Mu (inj₂ x₁) t₁ _ _ cs₁) (Mu (inj₂ x₂) t₂ _ _ cs₂) =
  let Γ' = ctxt-rename x₁ x₂ $ ctxt-var-decl x₂ Γ in
  conv-term Γ t₁ t₂ && conv-cases Γ' cs₁ cs₂
conv-term-norm Γ (Mu (inj₁ _) t₁ _ _ cs₁) (Mu (inj₁ _) t₂ _ _ cs₂) = conv-term Γ t₁ t₂ && conv-cases Γ cs₁ cs₂
{- it can happen that a term is equal to a lambda abstraction in head-normal form,
   if that lambda-abstraction would eta-contract following some further beta-reductions.
   We implement this here by implicitly eta-expanding the variable and continuing
   the comparison.

   A simple example is 

       λ v . t ((λ a . a) v) ≃ t
 -}
conv-term-norm Γ (Lam ff x _ t) t' =
  let x' = fresh-var Γ x in
  conv-term (ctxt-rename x x' Γ) t (App t' ff (Var x'))
conv-term-norm Γ t' (Lam ff x _ t) =
  let x' = fresh-var Γ x in
  conv-term (ctxt-rename x x' Γ) (App t' ff (Var x')) t 
conv-term-norm Γ _ _ = ff

conv-type-norm Γ (TpVar x) (TpVar x') = ctxt-eq-rep Γ x x'
conv-type-norm Γ (TpApp t1 t2) (TpApp t1' t2') = conv-type-norm Γ t1 t1' && conv-type Γ t2 t2'
conv-type-norm Γ (TpAppt t1 t2) (TpAppt t1' t2') = conv-type-norm Γ t1 t1' && conv-term Γ t2 t2'
conv-type-norm Γ (TpAbs me x atk tp) (TpAbs me' x' atk' tp') = 
  me iff me' && conv-tpkd Γ atk atk' && conv-type (ctxt-rename x x' (ctxt-var-decl-if x' Γ)) tp tp'
conv-type-norm Γ (TpIota x m tp) (TpIota x' m' tp') = 
  conv-type Γ m m' && conv-type (ctxt-rename x x' (ctxt-var-decl-if x' Γ)) tp tp'
conv-type-norm Γ (TpEq t₁ t₂) (TpEq t₁' t₂') = conv-term Γ t₁ t₁' && conv-term Γ t₂ t₂'
conv-type-norm Γ (TpLam x atk tp) (TpLam x' atk' tp') =
  conv-tpkd Γ atk atk' && conv-type (ctxt-rename x x' (ctxt-var-decl-if x' Γ)) tp tp'
conv-type-norm Γ _ _ = ff 

{- even though hnf turns Pi-kinds where the variable is not free in the body into arrow kinds,
   we still need to check off-cases, because normalizing the body of a kind could cause the
   bound variable to be erased (hence allowing it to match an arrow kind). -}
conv-kind-norm Γ (KdAbs x atk k) (KdAbs x' atk' k'') = 
    conv-tpkd Γ atk atk' && conv-kind (ctxt-rename x x' (ctxt-var-decl-if x' Γ)) k k''
conv-kind-norm Γ KdStar KdStar = tt
conv-kind-norm Γ _ _ = ff

conv-tpkd Γ tk tk' = conv-tpkde Γ (erase tk) (erase tk')

conv-tpkde Γ (Tkk k) (Tkk k') = conv-kind Γ k k'
conv-tpkde Γ (Tkt t) (Tkt t') = conv-type Γ t t'
conv-tpkde Γ _ _ = ff

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

conv-ctr Γ x₁ x₂ = conv-ctr-args Γ (x₁ , []) (x₂ , [])

conv-ctr-ps Γ x₁ x₂ with env-lookup Γ x₁ | env-lookup Γ x₂
...| just (ctr-def ps₁ T₁ n₁ i₁ a₁ , _) | just (ctr-def ps₂ T₂ n₂ i₂ a₂ , _) =
  maybe-if (n₁ =ℕ n₂ && i₁ =ℕ i₂ && a₁ =ℕ a₂) ≫maybe
  just (length (erase-params ps₁) , length (erase-params ps₂))
...| _ | _ = nothing

conv-ctr-args Γ (x₁ , as₁) (x₂ , as₂) =
  maybe-else' (conv-ctr-ps Γ x₁ x₂) ff $ uncurry λ ps₁ ps₂ →
  let as₁ = erase-args as₁; as₂ = erase-args as₂ in
  ps₁ ∸ length as₁ =ℕ ps₂ ∸ length as₂ &&
  conv-argse Γ (drop ps₁ as₁) (drop ps₂ as₂)


{-# TERMINATING #-}
inconv : ctxt → term → term → 𝔹
inconv Γ t₁ t₂ = inconv-lams empty-renamectxt empty-renamectxt
                   (hnf Γ unfold-all t₁ tt) (hnf Γ unfold-all t₂ tt)
  where
  fresh : var → renamectxt → renamectxt → var
  fresh x ρ₁ ρ₂ = fresh-h (λ x → ctxt-binds-var Γ x || renamectxt-in-field ρ₁ x || renamectxt-in-field ρ₂ x) x

  make-subst : renamectxt → renamectxt → 𝕃 var → 𝕃 var → term → term → (renamectxt × renamectxt × term × term)
  make-subst ρ₁ ρ₂ [] [] t₁ t₂ = ρ₁ , ρ₂ , t₁ , t₂
  make-subst ρ₁ ρ₂ (x₁ :: xs₁) [] t₁ t₂ =
    let x = fresh x₁ ρ₁ ρ₂ in
    make-subst (renamectxt-insert ρ₁ x₁ x) (renamectxt-insert ρ₂ x x) xs₁ [] t₁ (mapp t₂ $ Var x)
  make-subst ρ₁ ρ₂ [] (x₂ :: xs₂) t₁ t₂ =
    let x = fresh x₂ ρ₁ ρ₂ in
    make-subst (renamectxt-insert ρ₁ x x) (renamectxt-insert ρ₂ x₂ x) [] xs₂ (mapp t₁ $ Var x) t₂
  make-subst ρ₁ ρ₂ (x₁ :: xs₁) (x₂ :: xs₂) t₁ t₂ =
    let x = fresh x₁ ρ₁ ρ₂ in
    make-subst (renamectxt-insert ρ₁ x₁ x) (renamectxt-insert ρ₂ x₂ x) xs₁ xs₂ t₁ t₂
  
  inconv-lams : renamectxt → renamectxt → term → term → 𝔹
  inconv-apps : renamectxt → renamectxt → var → var → args → args → 𝔹
  inconv-ctrs : renamectxt → renamectxt → var → var → args → args → 𝔹
  inconv-mu : renamectxt → renamectxt → maybe (var × var) → cases → cases → 𝔹
  inconv-args : renamectxt → renamectxt → args → args → 𝔹

  inconv-args ρ₁ ρ₂ a₁ a₂ =
    let a₁ = erase-args a₁; a₂ = erase-args a₂ in
    ~  length a₁ =ℕ length a₂
    || list-any (uncurry $ inconv-lams ρ₁ ρ₂) (zip a₁ a₂)
  
  inconv-lams ρ₁ ρ₂ t₁ t₂ =
    elim-pair (decompose-lams t₁) λ l₁ b₁ →
    elim-pair (decompose-lams t₂) λ l₂ b₂ →
    elim-pair (make-subst ρ₁ ρ₂ l₁ l₂ b₁ b₂) λ ρ₁ ρ₂b₁₂ →
    elim-pair ρ₂b₁₂ λ ρ₂ b₁₂ →
    elim-pair b₁₂ λ b₁ b₂ →
    case (decompose-apps b₁ , decompose-apps b₂) of uncurry λ where
      (Var x₁ , a₁) (Var x₂ , a₂) →
        inconv-apps ρ₁ ρ₂ x₁ x₂ a₁ a₂ || inconv-ctrs ρ₁ ρ₂ x₁ x₂ a₁ a₂
      (Mu (inj₂ x₁) t₁ _ _ ms₁ , a₁) (Mu (inj₂ x₂) t₂ _ _ ms₂ , a₂) →
        inconv-mu ρ₁ ρ₂ (just $ x₁ , x₂) ms₁ ms₂ ||
        inconv-lams ρ₁ ρ₂ t₁ t₂ || inconv-args ρ₁ ρ₂ a₁ a₂
      (Mu (inj₁ _) t₁ _ _ ms₁ , a₁) (Mu (inj₁ _) t₂ _ _ ms₂ , a₂) →
        inconv-mu ρ₁ ρ₂ nothing ms₁ ms₂ ||
        inconv-lams ρ₁ ρ₂ t₁ t₂ || inconv-args ρ₁ ρ₂ a₁ a₂
      _ _ → ff

  inconv-apps ρ₁ ρ₂ x₁ x₂ a₁ a₂ =
    maybe-else' (renamectxt-lookup ρ₁ x₁) ff λ x₁ →
    maybe-else' (renamectxt-lookup ρ₂ x₂) ff λ x₂ →
    ~ x₁ =string x₂
    || inconv-args ρ₁ ρ₂ a₁ a₂

  inconv-ctrs ρ₁ ρ₂ x₁ x₂ as₁ as₂ with env-lookup Γ x₁ | env-lookup Γ x₂
  ...| just (ctr-def ps₁ _ n₁ i₁ a₁ , _) | just (ctr-def ps₂ _ n₂ i₂ a₂ , _) =
    let ps₁ = erase-params ps₁; ps₂ = erase-params ps₂
        as₁ = erase-args   as₁; as₂ = erase-args   as₂ in
    length as₁ ≤ length ps₁ + a₁ && -- Could use of "≤" here conflict with η-equality?
    length as₂ ≤ length ps₂ + a₂ &&
    (~ n₁ =ℕ n₂ ||
    ~ i₁ =ℕ i₂ ||
    ~ a₁ =ℕ a₂ ||
    ~ length as₁ + length ps₂ =ℕ length as₂ + length ps₁ ||
    -- ^ as₁ ∸ ps₁ ≠ as₂ ∸ ps₂, + ps₁ + ps₂ to both sides ^
    list-any (uncurry $ inconv-lams ρ₁ ρ₂)
      (zip (drop (length ps₁) as₁) (drop (length ps₂) as₂)))
  ...| _ | _ = ff

  inconv-mu ρ₁ ρ₂ xs? ms₁ ms₂ =
    ~ length ms₁ =ℕ length ms₂ ||
    maybe-else ff id
      (foldr {B = maybe 𝔹} (λ c b? → b? ≫=maybe λ b → inconv-case c ≫=maybe λ b' → just (b || b')) (just ff) ms₁)
    where
    matching-case : case → maybe (term × ℕ × ℕ)
    matching-case (Case x _ _) = foldl (λ where
      (Case xₘ cas tₘ) m? → m? maybe-or
        (conv-ctr-ps Γ xₘ x ≫=maybe uncurry λ psₘ ps →
         just (case-args-to-lams cas tₘ , length cas , ps)))
      nothing ms₂

    inconv-case : case → maybe 𝔹
    inconv-case c₁ @ (Case x cas₁ t₁) =
      matching-case c₁ ≫=maybe λ c₂ →
      just (inconv-lams ρ₁ ρ₂ (case-args-to-lams cas₁ t₁) (fst c₂))




ctxt-params-def : params → ctxt → ctxt
ctxt-params-def ps Γ@(mk-ctxt (fn , mn , _ , q) syms i symb-occs Δ) =
  mk-ctxt (fn , mn , ps , q) syms i symb-occs Δ

ctxt-kind-def : posinfo → var → params → kind → ctxt → ctxt
ctxt-kind-def pi v ps2 k Γ@(mk-ctxt (fn , mn , ps1 , q) (syms , mn-fn) i symb-occs Δ) = mk-ctxt
  (fn , mn , ps1 , qualif-insert-params q (mn # v) v ps1)
  (trie-insert-append2 syms fn mn v , mn-fn)
  (trie-insert i (mn # v) (kind-def (ps1 ++ ps2) k' , fn , pi))
  symb-occs Δ
  where
  k' = hnf Γ unfold-head k tt

ctxt-datatype-decl : var → var → args → ctxt → ctxt
ctxt-datatype-decl vₒ vᵣ as Γ@(mk-ctxt mod ss is os (Δ , μ' , μ , η)) =
  mk-ctxt mod ss is os $ Δ , trie-insert μ' (mu-Type/ vᵣ) (vₒ , mu-isType/ vₒ , as) , μ , stringset-insert η (mu-Type/ vᵣ)

ctxt-datatype-def : posinfo → var → params → kind → kind → ctrs → ctxt → ctxt
ctxt-datatype-def pi v psᵢ kᵢ k cs Γ@(mk-ctxt (fn , mn , ps , q) (syms , mn-fn) i os (Δ , μ' , μ , η)) =
  let v' = mn # v
      q' = qualif-insert-params q v' v ps in
  mk-ctxt (fn , mn , ps , q') 
    (trie-insert-append2 syms fn mn v , mn-fn)
    (trie-insert i v' (type-def (just ps) tt nothing (abs-expand-kind psᵢ k) , fn , pi)) os
    (trie-insert Δ v' (ps ++ psᵢ , kᵢ , k , cs) , μ' , trie-insert μ (data-Is/ v') v' , stringset-insert η v')

ctxt-type-def : posinfo → defScope → opacity → var → maybe type → kind → ctxt → ctxt
ctxt-type-def _  _ _ ignored-var _ _  Γ = Γ
ctxt-type-def pi s op v t k Γ@(mk-ctxt (fn , mn , ps , q) (syms , mn-fn) i symb-occs Δ) = mk-ctxt
  (fn , mn , ps , q')
  ((if (s iff localScope) then syms else trie-insert-append2 syms fn mn v) , mn-fn)
  (trie-insert i v' (type-def (def-params s ps) op t' k , fn , pi))
  symb-occs Δ
  where
  t' = maybe-map (λ t → hnf Γ unfold-head t tt) t
  v' = if s iff localScope then pi % v else mn # v
  q' = qualif-insert-params q v' v (if s iff localScope then [] else ps)

ctxt-ctr-def : posinfo → var → type → params → (ctrs-length ctr-index : ℕ) → ctxt → ctxt
ctxt-ctr-def pi c t ps' n i Γ@(mk-ctxt mod@(fn , mn , ps , q) (syms , mn-fn) is symb-occs Δ) = mk-ctxt
  (fn , mn , ps , q')
  ((trie-insert-append2 syms fn mn c) , mn-fn)  
  (trie-insert is c' (ctr-def (ps ++ ps') t n i (unerased-arrows t) , fn , pi))
  symb-occs Δ
  where
  c' = mn # c
  q' = qualif-insert-params q c' c ps

ctxt-term-def : posinfo → defScope → opacity → var → maybe term → type → ctxt → ctxt
ctxt-term-def _  _ _  ignored-var _ _ Γ = Γ
ctxt-term-def pi s op v t tp Γ@(mk-ctxt (fn , mn , ps , q) (syms , mn-fn) i symb-occs Δ) = mk-ctxt
  (fn , mn , ps , q')
  ((if (s iff localScope) then syms else trie-insert-append2 syms fn mn v) , mn-fn)
  (trie-insert i v' (term-def (def-params s ps) op t' tp , fn , pi))
  symb-occs Δ
  where
  t' = maybe-map (λ t → hnf Γ unfold-head t tt) t
  v' = if s iff localScope then pi % v else mn # v
  q' = qualif-insert-params q v' v (if s iff localScope then [] else ps)

ctxt-term-udef _ _ _ ignored-var _ Γ = Γ
ctxt-term-udef pi s op v t Γ@(mk-ctxt (fn , mn , ps , q) (syms , mn-fn) i symb-occs Δ) = mk-ctxt
  (fn , mn , ps , qualif-insert-params q v' v (if s iff localScope then [] else ps))
  ((if (s iff localScope) then syms else trie-insert-append2 syms fn mn v) , mn-fn)
  (trie-insert i v' (term-udef (def-params s ps) op t' , fn , pi))
  symb-occs Δ
  where
  t' = hnf Γ unfold-head t tt
  v' = if s iff localScope then pi % v else mn # v
