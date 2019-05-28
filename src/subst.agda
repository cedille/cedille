module subst where

open import lib

open import constants
open import cedille-types
open import ctxt-types
--open import is-free
open import free-vars
open import rename
open import general-util
open import syntax-util

substh-ret-t : Set → Set
substh-ret-t T = ctxt → renamectxt → trie (Σi exprd ⟦_⟧) → T → T

{-# TERMINATING #-}
substh : ∀ {ed} → substh-ret-t ⟦ ed ⟧
substh-arg : substh-ret-t arg
substh-args : substh-ret-t args
substh-params : substh-ret-t params
substh-cases : substh-ret-t cases
substh-case-args : ctxt → renamectxt → trie (Σi exprd ⟦_⟧) → case-args → case-args × renamectxt × ctxt

subst-rename-var-if : ctxt → renamectxt → var → trie (Σi exprd ⟦_⟧) → var
subst-rename-var-if Γ ρ "_" σ = "_"
subst-rename-var-if Γ ρ x σ =
  {- rename bound variable x iff it is one of the vars being substituted for, 
     or if x occurs free in one of the terms we are substituting for vars, 
     or if it is the renamed version of any variable -}
  if trie-contains σ x || trie-any (λ {(,_ {ed} t) → is-free-in x t}) σ || renamectxt-in-range ρ x || ctxt-binds-var Γ x then 
    fresh-h (λ s → ctxt-binds-var Γ s || trie-contains σ s || renamectxt-in-field ρ s) x
  else
    x

substh {TERM} Γ ρ σ (App t m t') = App (substh Γ ρ σ t) m (substh Γ ρ σ t')
substh {TERM} Γ ρ σ (AppTp t tp) = AppTp (substh Γ ρ σ t) (substh Γ ρ σ tp)
substh {TERM} Γ ρ σ (Lam me x oc t) =
  let x' = subst-rename-var-if Γ ρ x σ in
    Lam me x' (maybe-map (substh Γ ρ σ -tk_) oc) 
      (substh (ctxt-var-decl x' Γ) (renamectxt-insert ρ x x') σ t)
substh {TERM} Γ ρ σ (LetTm me x T t t') =
  let x' = subst-rename-var-if Γ ρ x σ in
    LetTm me x' (maybe-map (substh Γ ρ σ) T) (substh Γ ρ σ t)
      (substh (ctxt-var-decl x' Γ) (renamectxt-insert ρ x x') σ t')
substh {TERM} Γ ρ σ (LetTp x k T t) =
  let x' = subst-rename-var-if Γ ρ x σ in
    LetTp x' (substh Γ ρ σ k) (substh Γ ρ σ T)
      (substh (ctxt-var-decl x' Γ) (renamectxt-insert ρ x x') σ t)
substh {TERM} Γ ρ σ (Open o x t) = Open o (renamectxt-rep ρ x) (substh Γ ρ σ t)
substh {TERM} Γ ρ σ (Var x) =
 let x' = renamectxt-rep ρ x in
   case trie-lookup σ x' of λ where
     (just (,_ {TERM} t)) → t
     _ → Var x'
substh {TERM} Γ ρ σ (Hole pi) = Hole pi -- Retain position, so jumping to hole works
substh {TERM} Γ ρ σ (Beta ot ot') = Beta (maybe-map (substh Γ ρ σ) ot) (maybe-map (substh Γ ρ σ) ot')
substh {TERM} Γ ρ σ (IotaPair t₁ t₂ x T) =
  let x' = subst-rename-var-if Γ ρ x σ in
  IotaPair (substh Γ ρ σ t₁) (substh Γ ρ σ t₂) x (substh (ctxt-var-decl x' Γ) (renamectxt-insert ρ x x') σ T)
substh {TERM} Γ ρ σ (IotaProj t n) = IotaProj (substh Γ ρ σ t) n
substh {TERM} Γ ρ σ (Sigma t) = Sigma (substh Γ ρ σ t)
substh {TERM} Γ ρ σ (Phi t t₁ t₂) = Phi (substh Γ ρ σ t) (substh Γ ρ σ t₁) (substh Γ ρ σ t₂) 
substh {TERM} Γ ρ σ (Rho tₑ x T t) =
  let x' = subst-rename-var-if Γ ρ x σ in
  Rho (substh Γ ρ σ tₑ) x' (substh (ctxt-var-decl x' Γ) (renamectxt-insert ρ x x') σ T) (substh Γ ρ σ t)
substh {TERM} Γ ρ σ (Delta T t) = Delta (substh Γ ρ σ T) (substh Γ ρ σ t)
substh {TERM} Γ ρ σ (Mu (inj₂ x) t T t~ cs) =
  let fv = λ x → trie-contains σ x || ctxt-binds-var Γ x || renamectxt-in-field ρ x
      x' = fresh-h (λ x → fv x || fv (mu-Type/ x) || fv (mu-isType/ x)) x
      ρ' = renamectxt-insert ρ x x'
      ρ' = renamectxt-insert ρ' (mu-Type/ x) (mu-Type/ x')
      ρ' = renamectxt-insert ρ' (mu-isType/ x) (mu-isType/ x')
      Γ' = ctxt-var-decl x' Γ
      Γ' = ctxt-var-decl (mu-Type/ x') Γ'
      Γ' = ctxt-var-decl (mu-isType/ x') Γ' in
    Mu (inj₂ x') (substh Γ ρ σ t) (maybe-map (substh Γ ρ σ) T) t~ (substh-cases Γ' ρ' σ cs)
substh {TERM} Γ ρ σ (Mu (inj₁ t?) t' T t~ cs) =
  Mu (inj₁ (maybe-map (substh Γ ρ σ) t?)) (substh Γ ρ σ t') (maybe-map (substh Γ ρ σ) T) t~ (substh-cases Γ ρ σ cs)

substh {TYPE} Γ ρ σ (TpAbs me x tk t) =
  let x' = subst-rename-var-if Γ ρ x σ in
    TpAbs me x' (substh Γ ρ σ -tk tk)
      (substh (ctxt-var-decl x' Γ) (renamectxt-insert ρ x x') σ t)
substh {TYPE} Γ ρ σ (TpLam x tk t) =
  let x' = subst-rename-var-if Γ ρ x σ in
    TpLam x' (substh Γ ρ σ -tk tk) 
      (substh (ctxt-var-decl x' Γ) (renamectxt-insert ρ x x') σ t)
substh {TYPE} Γ ρ σ (TpIota x T₁ T₂) =
  let x' = subst-rename-var-if Γ ρ x σ in
    TpIota x' (substh Γ ρ σ T₁)
      (substh (ctxt-var-decl x' Γ) (renamectxt-insert ρ x x') σ T₂)
substh {TYPE} Γ ρ σ (TpApp tp tp₁) = TpApp (substh Γ ρ σ tp) (substh Γ ρ σ tp₁)
substh {TYPE} Γ ρ σ (TpAppt tp t) = TpAppt (substh Γ ρ σ tp) (substh Γ ρ σ t)
substh {TYPE} Γ ρ σ (TpEq t₁ t₂) = TpEq (substh Γ ρ σ t₁) (substh Γ ρ σ t₂)
substh {TYPE} Γ ρ σ (TpVar x) =
 let x' = renamectxt-rep ρ x in
   case trie-lookup σ x' of λ where
     (just (,_ {TYPE} T)) → T
     _ → TpVar x'
substh {TYPE} Γ ρ σ (TpHole pi) = TpHole pi -- Retain position, so jumping to hole works

substh {KIND} Γ ρ σ (KdAbs x tk k) =
  let x' = subst-rename-var-if Γ ρ x σ in
    KdAbs x' (substh Γ ρ σ -tk tk)
      (substh (ctxt-var-decl x' Γ) (renamectxt-insert ρ x x') σ k)
substh {KIND} Γ ρ σ KdStar = KdStar

substh-arg Γ ρ σ (TmArg me t) = TmArg me (substh Γ ρ σ t)
substh-arg Γ ρ σ (TpArg T) = TpArg (substh Γ ρ σ T)

substh-args Γ ρ σ = map (substh-arg Γ ρ σ)

substh-params Γ ρ σ ((Param me x tk) :: ps) =
  (Param me x (substh Γ ρ σ -tk tk) ) ::
    (substh-params Γ (renamectxt-insert ρ x x) (trie-remove σ x) ps)
substh-params Γ ρ σ [] = []

substh-cases Γ ρ σ = map λ where
  (Case x as t) →
    case (substh-case-args Γ ρ σ as) of λ where
      (as' , ρ' , Γ') → Case x as' (substh Γ' ρ' σ t)

substh-case-args Γ ρ σ as = foldr (λ where
  (CaseArg e x) f ρ Γ →
    let x' = subst-rename-var-if Γ ρ x σ in
    elim-pair (f (renamectxt-insert ρ x x') (ctxt-var-decl x' Γ)) λ as ρ-Γ →
    CaseArg e x' :: as , ρ-Γ)
  (λ ρ Γ → [] , ρ , Γ) as ρ Γ


subst-ret-t : Set → Set
subst-ret-t T = {ed : exprd} → ctxt → ⟦ ed ⟧ → var → T → T

subst : ∀ {ed} → subst-ret-t ⟦ ed ⟧
subst Γ t x = substh Γ empty-renamectxt (trie-single x (, t))

subst-cases : subst-ret-t cases
subst-cases Γ t x = substh-cases Γ empty-renamectxt (trie-single x (, t))

subst-renamectxt : ∀ {ed : exprd} → ctxt → renamectxt → ⟦ ed ⟧ → ⟦ ed ⟧
subst-renamectxt Γ ρ = substh Γ ρ empty-trie

rename-var : ∀ {ed} → ctxt → var → var → ⟦ ed ⟧ → ⟦ ed ⟧
rename-var Γ x x' = subst-renamectxt Γ (renamectxt-single x x')

substs-ret-t : Set → Set
substs-ret-t T = ctxt → trie (Σi exprd ⟦_⟧) → T → T

substs : ∀ {ed} → substs-ret-t ⟦ ed ⟧
substs = flip substh empty-renamectxt

substs-args : substs-ret-t args
substs-args = flip substh-args empty-renamectxt

substs-params : substs-ret-t params
substs-params = flip substh-params empty-renamectxt

substs-cases : substs-ret-t cases
substs-cases = flip substh-cases empty-renamectxt

subst-params-args : params → args → trie (Σi exprd ⟦_⟧) × params × args
subst-params-args ps as = subst-params-args' ps as empty-trie where
  subst-params-args' : params → args → trie (Σi exprd ⟦_⟧) → trie (Σi exprd ⟦_⟧) × params × args
  subst-params-args' (Param me x tk :: ps) (TmArg me' t :: as) σ =
    subst-params-args' ps as (trie-insert σ x (, t))
  subst-params-args' (Param me x tk :: ps) (TpArg T :: as) σ =
    subst-params-args' ps as (trie-insert σ x (, T))
  subst-params-args' ps as σ = σ , ps , as

subst-params-args' : ctxt → params → args → ∀ {ed} → ⟦ ed ⟧ → ⟦ ed ⟧ × params × args
subst-params-args' Γ ps as t = map-fst (λ σ → substs Γ σ t) (subst-params-args ps as)

infixr 3 [_-_/_]_
[_-_/_]_ : ∀ {ed ed'} → ctxt → ⟦ ed ⟧ → var → ⟦ ed' ⟧ → ⟦ ed' ⟧
[ Γ - t / x ] t' = subst Γ t x t'
