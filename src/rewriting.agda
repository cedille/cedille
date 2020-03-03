module rewriting where

open import ial-datatypes
open import cedille-types
open import constants
open import conversion ff
  using (conv-term ; hnf ; unfold-head ; unfold-head-elab ; conv-type ; unfold-no-defs ; unfold ; unfold-all)
open import ctxt
open import general-util
open import free-vars
--open import lift
open import rename
open import subst
open import syntax-util
open import type-util
--open import erase
open import datatype-util

rewrite-mk-phi : var → (eq t t' : term) → term
rewrite-mk-phi x eq t t' =
  Phi (Rho (VarSigma eq) x (TpEq t t') (Beta t id-term)) t t'

rewrite-t : Set → Set
rewrite-t T = ctxt → (is-plus : 𝔹) → (nums : maybe stringset) → (eq : maybe term) →
              (left : term) → (right : var) → (total-matches : ℕ) →
              T {- Returned value -} ×
              ℕ {- Number of rewrites actually performed -} ×
              ℕ {- Total number of matches, including skipped ones -}

instance
  rewrite-functor : functor rewrite-t
  rewrite-applicative : applicative rewrite-t
  rewrite-monad : monad rewrite-t
  
  fmap ⦃ rewrite-functor ⦄ g r Γ op on eq t₁ t₂ n with r Γ op on eq t₁ t₂ n
  ...| a , n' , sn = g a , n' , sn
  
  pure ⦃ rewrite-applicative ⦄ a Γ p on eq t₁ t₂ n = a , 0 , n
  _<*>_ ⦃ rewrite-applicative ⦄ f a Γ op on eq t₁ t₂ n with f Γ op on eq t₁ t₂ n
  ...| f' , n' , sn with a Γ op on eq t₁ t₂ sn
  ...| b , n'' , sn' = f' b , n' + n'' , sn'

  return ⦃ rewrite-monad ⦄ a = pure a
  _>>=_ ⦃ rewrite-monad ⦄ fa fab Γ op on eq t₁ t₂ n with fa Γ op on eq t₁ t₂ n
  ...| a' , n' , sn with fab a' Γ op on eq t₁ t₂ sn
  ...| b , n'' , sn' = b , n' + n'' , sn'

infixl 4 _≫rewrite_
_≫rewrite_ = _<*>_


{-# TERMINATING #-}
rewrite-term  : term → rewrite-t term
rewrite-terma : term → rewrite-t term
rewrite-termh : term → rewrite-t term
rewrite-type  : type → rewrite-t type
rewrite-typeh : type → rewrite-t type
rewrite-kind  : kind → rewrite-t kind
rewrite-tpkd  : tpkd → rewrite-t tpkd
rewrite-tmtp  : tmtp → rewrite-t tmtp
rewrite-exprd : ∀ {ed} → ⟦ ed ⟧ → rewrite-t ⟦ ed ⟧
rewrite-case  : maybe (var × var) → case → rewrite-t case

rewrite-exprd {TERM} = rewrite-term
rewrite-exprd {TYPE} = rewrite-type
rewrite-exprd {KIND} = rewrite-kind

rewrite-rename-var : ∀ {A} → var → (var → rewrite-t A) → rewrite-t A
rewrite-rename-var x r Γ op on eq t₁ t₂ n =
  let x' = rename-var-if Γ (renamectxt-insert empty-renamectxt t₂ t₂) x t₁ in
  r x' Γ op on eq t₁ t₂ n

rewrite-abs : ∀ {ed} → var → var → (⟦ ed ⟧ → rewrite-t ⟦ ed ⟧) → ⟦ ed ⟧ → rewrite-t ⟦ ed ⟧
rewrite-abs x x' g a Γ = let Γ = ctxt-var-decl x' Γ in g (rename-var Γ x x' a) Γ

rewrite-term t Γ op on eq t₁ t₂ sn =
  case rewrite-terma (erase t) Γ op on eq t₁ t₂ sn of λ where
    (t' , 0 , sn') → t , 0 , sn'
    (t' , n , sn') → maybe-else' eq t' (λ eq → rewrite-mk-phi t₂ eq t t') , n , sn'

-- dont disable this one
rewrite-terma t Γ op on eq t₁ t₂ sn =
  case conv-term Γ t t₁ of λ where
  tt → case on of λ where
    (just ns) → case trie-contains ns (ℕ-to-string (suc sn)) of λ where
      tt → Var t₂ , 1 , suc sn -- ρ nums contains n
      ff → t , 0 , suc sn -- ρ nums does not contain n
    nothing → Var t₂ , 1 , suc sn
  ff → case op of λ where
    tt → case rewrite-termh (hnf Γ unfold-head t) Γ op on eq t₁ t₂ sn of λ where
      (t' , 0 , sn') → t , 0 , sn' -- if no rewrites were performed, return the pre-hnf t
      (t' , n' , sn') → t' , n' , sn'
    ff → rewrite-termh t Γ op on eq t₁ t₂ sn

rewrite-termh (App t t') =
  pure App <*> rewrite-terma t <*> rewrite-terma t'
rewrite-termh (Lam NotErased y nothing t) =
  rewrite-rename-var y λ y' → pure (Lam NotErased y' nothing) <*>
  rewrite-abs y y' rewrite-terma t
rewrite-termh (Var x) = pure (Var x)
rewrite-termh (LetTm ff x nothing t t') Γ = rewrite-terma (subst Γ t x t') Γ
--  rewrite-rename-var x λ x' → pure (Let pi₁) <*>
--  (pure (DefTerm pi₂ x' NoType) <*> rewrite-terma t) <*>
--  rewrite-abs x x' rewrite-terma t'
-- ^^^ Need to DEFINE "x" as "hnf Γ unfold-head t tt", not just declare it!
--     We may instead simply rewrite t' after substituting t for x
rewrite-termh (Mu x t nothing t~ ms) =
  rewrite-rename-var x λ x' →
  pure (Mu x') <*>
  rewrite-terma t <*>
  pure nothing <*>
  pure t~ <*>
  foldr (λ c r → pure _::_ <*> rewrite-case (just $ x , x') c <*> r)
    (pure []) ms
rewrite-termh (Sigma tᵢ t nothing t~ ms) =
  pure (Sigma tᵢ) <*>
  rewrite-terma t <*>
  pure nothing <*>
  pure t~ <*>
  foldr (λ c r → pure _::_ <*> rewrite-case nothing c <*> r)
    (pure []) ms
rewrite-termh = pure

rewrite-case xᵣ? (Case x cas t T) =
  let f = maybe-else' xᵣ? id (uncurry rewrite-abs) rewrite-terma in
  pure (uncurry $ Case x) <*>
  foldr {B = rewrite-t case-args → (term → rewrite-t term) → rewrite-t (case-args × term)}
    (λ {(CaseArg ff x nothing) r cas fₜ →
      r (rewrite-rename-var x λ x' → pure _::_ <*> pure (CaseArg ff x' nothing) <*> cas) (λ t → rewrite-rename-var x λ x' → rewrite-abs x x' fₜ t); _ → id})
    (λ cas fₜ → pure (_,_ ∘ reverse) <*> cas <*> fₜ t) cas (pure []) f <*> return T

rewrite-type T Γ tt on eq t₁ t₂ sn
  with rewrite-typeh (hnf Γ unfold-head-elab T) Γ tt on eq t₁ t₂ sn
...| T' , 0 , sn' = T  , 0 , sn'
...| T' , n , sn' = T' , n , sn'
rewrite-type = rewrite-typeh

rewrite-typeh (TpAbs me x atk T) =
  rewrite-rename-var x λ x' → 
  pure (TpAbs me x') <*> rewrite-tpkd atk <*>
  rewrite-abs x x' rewrite-type T
rewrite-typeh (TpIota x T T') =
  rewrite-rename-var x λ x' →
  pure (TpIota x') <*> rewrite-type T <*>
  rewrite-abs x x' rewrite-type T'
rewrite-typeh (TpApp T tT) =
  pure TpApp <*> rewrite-typeh T <*> rewrite-tmtp tT
rewrite-typeh (TpEq t₁ t₂) =
  pure TpEq <*> (pure erase <*> rewrite-term t₁) <*>
  (pure erase <*> rewrite-term t₂)
rewrite-typeh (TpLam x atk T) =
  rewrite-rename-var x λ x' →
  pure (TpLam x') <*> rewrite-tpkd atk <*>
  rewrite-abs x x' rewrite-type T
rewrite-typeh (TpHole pi) = pure (TpHole pi)
rewrite-typeh (TpVar x) = pure (TpVar x)

-- If we ever implement kind-level rewriting, we will need to go through
-- all the types of kind pi binding a term or type-to-kind arrow
-- if the right-hand side variable is free in the types of the bound variable,
-- and substitute each occurence of the term variable (eta-expanding if necessary)
-- in the body of the type with itself surrounded by a rewrite back the original
-- expected type (unless we lifted a term, then it gets really tricky because
-- we may not want to rewrite back?).
rewrite-kind = pure
rewrite-liftingType = pure

rewrite-tpkd (Tkt T) = pure Tkt <*> rewrite-type T
rewrite-tpkd (Tkk k) = pure Tkk <*> rewrite-kind k

rewrite-tmtp (Ttm t) = pure Ttm <*> rewrite-term t
rewrite-tmtp (Ttp T) = pure Ttp <*> rewrite-type T

post-rewrite-binder-type : ∀ {ed} → ctxt → var → term → (var → tpkd → ctxt → ctxt) → var → ⟦ ed ⟧ → type → ⟦ ed ⟧
post-rewrite-binder-type Γ x eq tk-decl x' Tₓ Tₓ' with is-free-in x Tₓ'
...| ff = Tₓ
...| tt = subst (tk-decl x' (Tkt Tₓ') Γ) (Rho eq x Tₓ' (Var x')) x' Tₓ

post-rewrite-binder-kind : ∀ {ed} → ctxt → var → term → (var → tpkd → ctxt → ctxt) → var → ⟦ ed ⟧ → kind → ⟦ ed ⟧
post-rewrite-binder-kind Γ x eq tk-decl x' Tₓ kₓ' = Tₓ

post-rewrite-binder-tk : ∀ {ed} → ctxt → var → term → (var → tpkd → ctxt → ctxt) → var → ⟦ ed ⟧ → tpkd → ⟦ ed ⟧
post-rewrite-binder-tk Γ x eq tk-decl x' Tₓ (Tkt Tₓ') =
  post-rewrite-binder-type Γ x eq tk-decl x' Tₓ Tₓ'
post-rewrite-binder-tk Γ x eq tk-decl x' Tₓ (Tkk kₓ') =
  post-rewrite-binder-kind Γ x eq tk-decl x' Tₓ kₓ'

post-rewriteh : ctxt → var → term → (ctxt → var → term → tpkd → tpkd) → (var → tpkd → ctxt → ctxt) → type → type × kind

post-rewriteh Γ x eq prtk tk-decl (TpAbs me x' atk T) =
  let atk = prtk Γ x eq atk
      T = fst $ post-rewriteh (tk-decl x' atk Γ) x eq prtk tk-decl T
      T = post-rewrite-binder-tk Γ x eq tk-decl x' T atk in
  TpAbs me x' atk T , KdStar
post-rewriteh Γ x eq prtk tk-decl (TpIota x' T T') =
  let T = fst $ post-rewriteh Γ x eq prtk tk-decl T
      T' = fst $ post-rewriteh (tk-decl x' (Tkt T) Γ) x eq prtk tk-decl T'
      T' = post-rewrite-binder-type Γ x eq tk-decl x' T' T in
  TpIota x' T T' , KdStar
post-rewriteh Γ x eq prtk tk-decl (TpApp T (Ttp T')) =
  elim-pair (post-rewriteh Γ x eq prtk tk-decl T') λ T' k' →
  elim-pair (post-rewriteh Γ x eq prtk tk-decl T) λ where
    T (KdAbs x' atk k) → TpApp T (Ttp T') , hnf Γ unfold-head-elab (subst Γ T' x' k)
    T k → TpApp T (Ttp T') , k
post-rewriteh Γ x eq prtk tk-decl (TpApp T (Ttm t)) =
  let t2 T' = if is-free-in x T' then Rho (VarSigma eq) x T' t else t in
  elim-pair (post-rewriteh Γ x eq prtk tk-decl T) λ where
    T (KdAbs x' (Tkt T') k) →
      let t3 = t2 T' in TpApp T (Ttm t3) , hnf Γ unfold-head-elab (subst Γ t3 x' k)
    T k → TpApp T (Ttm t) , k
post-rewriteh Γ x eq prtk tk-decl (TpLam x' atk T) =
  let atk = prtk Γ x eq atk in
  elim-pair (post-rewriteh (tk-decl x' atk Γ) x eq prtk tk-decl T) λ T k →
  let T = post-rewrite-binder-tk Γ x eq tk-decl x' T atk
      k = post-rewrite-binder-tk Γ x eq tk-decl x' k atk in
  TpLam x' atk T , KdAbs x' atk k
post-rewriteh Γ x eq prtk tk-decl (TpVar x') with env-lookup Γ x'
...| just (type-decl k , _) = TpVar x' , hnf Γ unfold-head-elab k
...| just (type-def mps _ T k , _) = TpVar x' , (hnf Γ unfold-head-elab (maybe-else id abs-expand-kind mps k))
...| _ = TpVar x' , KdStar
post-rewriteh Γ x eq prtk tk-decl T = T , KdStar

{-# TERMINATING #-}
post-rewrite : ctxt → var → (eq t₂ : term) → type → type
post-rewrite Γ x eq t₂ T = subst Γ t₂ x (fst (post-rewriteh Γ x eq prtk tk-decl T)) where
  prtk : ctxt → var → term → tpkd → tpkd
  tk-decl : var → tpkd → ctxt → ctxt
  prtk Γ x t (Tkt T) = Tkt (fst (post-rewriteh Γ x t prtk tk-decl T))
  prtk Γ x t (Tkk k) = Tkk (hnf Γ unfold-head-elab k)
  tk-decl x atk Γ =
    record Γ { i = trie-insert (ctxt.i Γ) x (either-else' atk term-decl type-decl , "" , "") }

-- Functions for substituting the type T in ρ e @ x . T - t
rewrite-at-t : Set → Set
rewrite-at-t X = ctxt → var → maybe term → 𝔹 → X → X → X
{-# TERMINATING #-}
rewrite-at : rewrite-at-t type
rewrite-at' : ∀ {ed} → rewrite-at-t ⟦ ed ⟧ → rewrite-at-t ⟦ ed ⟧
rewrite-ath : rewrite-at-t type
rewrite-atₖ : rewrite-at-t kind
rewrite-athₖ : rewrite-at-t kind
rewrite-at-tk : rewrite-at-t tpkd

rewrite-at-tk Γ x eq b (Tkt T) (Tkt T') = Tkt (rewrite-at Γ x eq b T T')
rewrite-at-tk Γ x eq b (Tkk k) (Tkk k') = Tkk (rewrite-atₖ Γ x eq b k k')
rewrite-at-tk Γ x eq b atk1 atk2 = atk1

rewrite-at = rewrite-at' rewrite-ath
rewrite-atₖ = rewrite-at' rewrite-athₖ


rewrite-head-types-match : ∀ {ed} → ctxt → var → (complete partial : ⟦ ed ⟧) → 𝔹
rewrite-head-types-match{TYPE} Γ x (TpApp T _) (TpApp T' _) = conv-type Γ T ([ Γ - Hole pi-gen / x ] T')
rewrite-head-types-match Γ x T T' = tt

rewrite-at' ra Γ x eq b T T' =
  if ~ is-free-in x T'
    then T
    else if b && ~ rewrite-head-types-match Γ x T T'
      then ra Γ x eq ff (hnf Γ unfold-head-elab T) (hnf Γ unfold-head-elab T')
      else ra Γ x eq b T T'


rewrite-athₖ Γ x eq b (KdAbs x1 atk1 k1) (KdAbs x2 atk2 k2) =
  KdAbs x1 (rewrite-at-tk Γ x eq tt atk1 atk2) (rewrite-atₖ (ctxt-var-decl x1 Γ) x eq tt k1 $ rename-var Γ x2 x1 k2)
rewrite-athₖ Γ x eq b KdStar KdStar = KdStar
rewrite-athₖ Γ x eq tt k1 k2 = rewrite-atₖ Γ x eq ff (hnf Γ unfold-head-elab k1) (hnf Γ unfold-head-elab k2)
rewrite-athₖ Γ x eq ff k1 k2 = k1

rewrite-ath Γ x eq b (TpAbs me1 x1 atk1 T1) (TpAbs me2 x2 atk2 T2) =
  TpAbs me1 x1 (rewrite-at-tk Γ x eq tt atk1 atk2) (rewrite-at (ctxt-var-decl x1 Γ) x eq tt T1 (rename-var Γ x2 x1 T2))
rewrite-ath Γ x eq b (TpIota x1 T1 T1') (TpIota x2 T2 T2') =
  TpIota x1 (rewrite-at Γ x eq tt T1 T2) (rewrite-at (ctxt-var-decl x1 Γ) x eq tt T1' (rename-var Γ x2 x1 T2'))
rewrite-ath Γ x eq b (TpApp T1 (Ttp T1')) (TpApp T2 (Ttp T2')) =
  TpApp (rewrite-at Γ x eq b T1 T2) (Ttp (rewrite-at Γ x eq tt T1' T2'))
rewrite-ath Γ x eq b (TpApp T1 (Ttm t1)) (TpApp T2 (Ttm t2)) = 
  TpApp (rewrite-at Γ x eq b T1 T2) (Ttm (maybe-else' (ifMaybe (is-free-in x t2) eq) t1 λ eq → rewrite-mk-phi x eq t1 t2))
rewrite-ath Γ x eq b (TpEq t1 t1') (TpEq t2 t2') =
  TpEq t2 t2'
rewrite-ath Γ x eq b (TpLam x1 atk1 T1) (TpLam x2 atk2 T2) =
  TpLam x1 (rewrite-at-tk Γ x eq tt atk1 atk2) (rewrite-at (ctxt-var-decl x1 Γ) x eq tt T1 (rename-var Γ x2 x1 T2))
rewrite-ath Γ x eq b (TpVar x1) (TpVar x2) = TpVar x1
rewrite-ath Γ x eq b (TpHole pi1) (TpHole pi2) = TpHole pi1
rewrite-ath Γ x eq tt T1 T2 = rewrite-at Γ x eq ff (hnf Γ unfold-head-elab T1) (hnf Γ unfold-head-elab T2)
rewrite-ath Γ x eq ff T1 T2 = T1

hnf-ctr : ctxt → var → type → type
hnf-ctr Γ x T = hnf Γ unfold-no-defs (rewrite-at Γ x nothing tt (hnf Γ (unfold tt ff ff) T) $ hnf Γ (record unfold-all {unfold-erase = ff}) T)



{-# TERMINATING #-}
refine-term : ctxt → tmtp → var → term → term
refine-type : ctxt → tmtp → var → type → type
refine-typeh : ctxt → tmtp → var → type → type
refine-kind : ctxt → tmtp → var → kind → kind
refine : ∀ {ed} → ctxt → tmtp → var → ⟦ ed ⟧ → ⟦ ed ⟧

refine {TERM} = refine-term
refine {TYPE} = refine-type
refine {KIND} = refine-kind

refine-term Γ (Ttp T) to t = t
refine-term Γ (Ttm t') to t with rewrite-term t Γ ff nothing nothing t' to 0
...| t'' , zero , _ = t
...| t'' , suc _ , _ = t''

refine-type Γ fm to T =
  if either-else' fm (const ff) (conv-type Γ T)
    then TpVar to
    else refine-typeh Γ fm to T

refine-typeh Γ fm to (TpAbs me x atk T) =
  let x' = fresh-var Γ x in 
  TpAbs me x' (refine Γ fm to -tk atk) (refine-type (ctxt-var-decl x' Γ) fm to (rename-var Γ x x' T))
refine-typeh Γ fm to (TpIota x T T') =
  let x' = fresh-var Γ x in
  TpIota x' (refine-type Γ fm to T) (refine-type (ctxt-var-decl x' Γ) fm to (rename-var Γ x x' T'))
refine-typeh Γ fm to (TpApp T tT) =
   TpApp (refine-type Γ fm to T) (refine Γ fm to -tT tT)
refine-typeh Γ fm to (TpEq t₁ t₂) =
  TpEq (refine-term Γ fm to t₁) (refine-term Γ fm to t₂)
refine-typeh Γ fm to (TpLam x atk T) =
  let x' = fresh-var Γ x in
  TpLam x' (refine Γ fm to -tk atk) (refine-type (ctxt-var-decl x' Γ) fm to (rename-var Γ x x' T))
refine-typeh Γ fm to (TpHole pi) = TpHole pi
refine-typeh Γ fm to (TpVar x) = TpVar x

refine-kind Γ fm to (KdAbs x atk k) =
  let x' = fresh-var Γ x in
  KdAbs x (refine Γ fm to -tk atk) (refine-kind (ctxt-var-decl x' Γ) fm to (rename-var Γ x x' k))
refine-kind Γ fm to (KdHole pi) = KdHole pi
refine-kind Γ fm to KdStar = KdStar

refine-motive : ctxt → indices → (asᵢ : 𝕃 tmtp) → (expected : type) → type
refine-motive Γ is as =
  foldr
    (λ where
      (Index x atk , ty) f Γ T →
        let body = f (ctxt-var-decl x Γ) $ refine-type (ctxt-var-decl x Γ) ty x T
            x' = if is-free-in x body then x else ignored-var in
        TpLam x' atk body)
    (λ Γ T → T) (zip (rename-indices Γ is as) as) Γ

-- Given a context, the (qualified) scrutinee, the (qualified) datatype name,
-- the datatype's indices, the arguments for module parameter instantiation,
-- the arguments for the indices in the type of the scrutinee, and the expected type,
-- calculate a possibly ill-typed motive that is approximately abstracted over the
-- indices and the scrutinee itself.
{-
refine-motive : ctxt → (scrutinee : term) → (datatype-name : var) → indices → (mod-as : 𝕃 tty) → (idx-as : 𝕃 tty) → (expected : type) → type
refine-motive Γ t name is asₚ asᵢ =
  let x = fresh-var (add-indices-to-ctxt is Γ) "x"
      atkₓ = Tkt $ indices-to-tpapps is $ recompose-tpapps asₚ $ TpVar pi-gen name
      as' = asᵢ ++ [ tterm t ]
      is' = rename? Γ empty-renamectxt (is ++ [ Index x atkₓ ]) as'
      as = zip is' as' in
  foldr
    (λ where
      (Index x atk , ty) f Γ T →
        TpLambda pi-gen pi-gen x atk $ f (ctxt-var-decl x Γ) $
          refine-type (ctxt-var-decl x Γ) ty x T)
    (λ Γ T → T) as Γ
  where
  get-var : var → tty → var
  get-var x (tterm (Var _ x')) = maybe-else (unqual-local x') id $ var-suffix x'
  get-var x (ttype (TpVar _ x')) = maybe-else (unqual-local x') id $ var-suffix x'
  get-var x _ = x

  rename? : ctxt → renamectxt → indices → 𝕃 tty → indices
  rename? Γ ρ (Index x atk :: is) (ty :: tys) =
    let x' = get-var x ty in
    Index x' (subst-renamectxt Γ ρ atk) :: rename? (ctxt-var-decl x' Γ) (renamectxt-insert ρ x x') is tys
  rename? _ _ _ _ = []
-}
