module subst where

open import constants
open import cedille-types
open import ctxt-types
open import free-vars
open import rename
open import general-util
open import syntax-util
open import type-util

substh-ret-t : Set → Set
substh-ret-t T = ctxt → renamectxt → trie (Σi exprd ⟦_⟧) → T → T

{-# TERMINATING #-}
substh : ∀ {ed} → substh-ret-t ⟦ ed ⟧
substh-arg : substh-ret-t arg
substh-args : substh-ret-t args
substh-params' : ctxt → renamectxt → trie (Σi exprd ⟦_⟧) → params → params × ctxt × renamectxt × trie (Σi exprd ⟦_⟧)
substh-indices : substh-ret-t indices
substh-params : substh-ret-t params
substh-case : substh-ret-t case
substh-cases : substh-ret-t cases
substh-case-args : ctxt → renamectxt → trie (Σi exprd ⟦_⟧) → case-args → case-args × renamectxt × ctxt × trie (Σi exprd ⟦_⟧)
substh-datatype-info : substh-ret-t datatype-info

subst-rename-var-if : ∀ {ed} → ctxt → renamectxt → var → trie (Σi exprd ⟦_⟧) → ⟦ ed ⟧ → var
subst-rename-var-if Γ ρ ignored-var σ t =
  if is-free-in ignored-var t
  then fresh-h (λ s → ctxt-binds-var Γ s || trie-contains σ s || renamectxt-in-field ρ s) "x"
  else ignored-var
subst-rename-var-if Γ ρ x σ _ =
  {- rename bound variable x iff it is one of the vars being substituted for,
     or if x occurs free in one of the terms we are substituting for vars,
     or if it is the renamed version of any variable -}
  if trie-contains σ x {-|| trie-any (λ {(,_ {ed} t) → is-free-in x t}) σ-}
     || renamectxt-in-range ρ x || ctxt-binds-var Γ x
  then fresh-h (λ s → ctxt-binds-var Γ s || trie-contains σ s || renamectxt-in-field ρ s) x
  else x

substh {TERM} Γ ρ σ (App t t') = App (substh Γ ρ σ t) (substh Γ ρ σ t')
substh {TERM} Γ ρ σ (AppE t tT) = AppE (substh Γ ρ σ t) (substh Γ ρ σ -tT tT)
substh {TERM} Γ ρ σ (Lam me x oc t) =
  let x' = subst-rename-var-if Γ ρ x σ t in
    Lam me x' (substh Γ ρ σ -tk_ <$> oc)
      (substh (ctxt-var-decl x' Γ) (renamectxt-insert ρ x x') σ t)
substh {TERM} Γ ρ σ (LetTm me x T t t') =
  let x' = subst-rename-var-if Γ ρ x σ t' in
    LetTm me x' (substh Γ ρ σ <$> T) (substh Γ ρ σ t)
      (substh (ctxt-var-decl x' Γ) (renamectxt-insert ρ x x') σ t')
substh {TERM} Γ ρ σ (LetTp x k T t) =
  let x' = subst-rename-var-if Γ ρ x σ t in
    LetTp x' (substh Γ ρ σ k) (substh Γ ρ σ T)
      (substh (ctxt-var-decl x' Γ) (renamectxt-insert ρ x x') σ t)
substh {TERM} Γ ρ σ (Var x) =
 let x' = renamectxt-rep ρ x in
   case trie-lookup σ x' of λ where
     (just (,_ {TERM} t)) → t
     _ → Var x'
substh {TERM} Γ ρ σ (Hole pi) = Hole pi -- Retain position, so jumping to hole works
substh {TERM} Γ ρ σ (Beta t t') = Beta (substh Γ ρ σ t) (substh Γ ρ σ t')
substh {TERM} Γ ρ σ (IotaPair t₁ t₂ x T) =
  let x' = subst-rename-var-if Γ ρ x σ T in
  IotaPair (substh Γ ρ σ t₁) (substh Γ ρ σ t₂) x' (substh (ctxt-var-decl x' Γ) (renamectxt-insert ρ x x') σ T)
substh {TERM} Γ ρ σ (IotaProj t n) = IotaProj (substh Γ ρ σ t) n
substh {TERM} Γ ρ σ (VarSigma t) = VarSigma (substh Γ ρ σ t)
substh {TERM} Γ ρ σ (Phi t t₁ t₂) = Phi (substh Γ ρ σ t) (substh Γ ρ σ t₁) (substh Γ ρ σ t₂)
substh {TERM} Γ ρ σ (Rho tₑ x T t) =
  let x' = subst-rename-var-if Γ ρ x σ T in
  Rho (substh Γ ρ σ tₑ) x' (substh (ctxt-var-decl x' Γ) (renamectxt-insert ρ x x') σ T) (substh Γ ρ σ t)
substh {TERM} Γ ρ σ (Delta b? T t) =
  Delta (b? >>=c λ t₁ t₂ → just (substh Γ ρ σ t₁ , substh Γ ρ σ t₂))
        (substh Γ ρ σ T) (substh Γ ρ σ t)
substh {TERM} Γ ρ σ (Mu x t T t~ ms) =
  let fv = λ x → trie-contains σ x || ctxt-binds-var Γ x || renamectxt-in-field ρ x
      x' = fresh-h (λ x → fv x || fv (mu-Type/ x) || fv (mu-isType/ x))
                   (if x =string ignored-var then "x" else x)
      ρ' = renamectxt-insert ρ x x'
      ρ' = renamectxt-insert ρ' (mu-Type/ x) (mu-Type/ x')
      ρ' = renamectxt-insert ρ' (mu-isType/ x) (mu-isType/ x')
      Γ' = ctxt-var-decl x' Γ
      Γ' = ctxt-var-decl (mu-Type/ x') Γ'
      Γ' = ctxt-var-decl (mu-isType/ x') Γ' in
    Mu x' (substh Γ ρ σ t) (substh (ctxt-var-decl (mu-Type/ x') Γ) (renamectxt-insert ρ (mu-Type/ x) (mu-Type/ x')) σ <$> T) (substh-datatype-info Γ ρ σ t~) (substh-cases Γ' ρ' σ ms)
substh {TERM} Γ ρ σ (Sigma tᵢ t' T t~ ms) =
  Sigma (substh Γ ρ σ <$> tᵢ) (substh Γ ρ σ t') (substh Γ ρ σ <$> T) (substh-datatype-info Γ ρ σ t~) (substh-cases Γ ρ σ ms)

substh {TYPE} Γ ρ σ (TpAbs me x tk t) =
  let x' = subst-rename-var-if Γ ρ x σ t in
    TpAbs me x' (substh Γ ρ σ -tk tk)
      (substh (ctxt-var-decl x' Γ) (renamectxt-insert ρ x x') σ t)
substh {TYPE} Γ ρ σ (TpLam x tk t) =
  let x' = subst-rename-var-if Γ ρ x σ t in
    TpLam x' (substh Γ ρ σ -tk tk)
      (substh (ctxt-var-decl x' Γ) (renamectxt-insert ρ x x') σ t)
substh {TYPE} Γ ρ σ (TpIota x T₁ T₂) =
  let x' = subst-rename-var-if Γ ρ x σ T₂ in
    TpIota x' (substh Γ ρ σ T₁)
      (substh (ctxt-var-decl x' Γ) (renamectxt-insert ρ x x') σ T₂)
substh {TYPE} Γ ρ σ (TpApp tp tT) = TpApp (substh Γ ρ σ tp) (substh Γ ρ σ -tT tT)
substh {TYPE} Γ ρ σ (TpEq t₁ t₂) = TpEq (substh Γ ρ σ t₁) (substh Γ ρ σ t₂)
substh {TYPE} Γ ρ σ (TpVar x) =
 let x' = renamectxt-rep ρ x in
   case trie-lookup σ x' of λ where
     (just (,_ {TYPE} T)) → T
     _ → TpVar x'
substh {TYPE} Γ ρ σ (TpHole pi) = TpHole pi -- Retain position, so jumping to hole works

substh {KIND} Γ ρ σ (KdAbs x tk k) =
  let x' = subst-rename-var-if Γ ρ x σ k in
    KdAbs x' (substh Γ ρ σ -tk tk)
      (substh (ctxt-var-decl x' Γ) (renamectxt-insert ρ x x') σ k)
substh {KIND} Γ ρ σ (KdHole pi) = KdHole pi -- Retain position, so jumping to hole works
substh {KIND} Γ ρ σ KdStar = KdStar

substh-datatype-info Γ ρ σ (mk-data-info X Xₒ asₚ asᵢ ps kᵢ k cs csₚₛ gds eds) =
  let Γ' = foldr (λ { (Param me x tk) Γ → ctxt-var-decl x Γ       }) Γ ps
      ρ' = foldr (λ { (Param me x tk) ρ → renamectxt-insert ρ x x }) ρ ps
      σ' = foldr (λ { (Param me x tk) σ → trie-remove σ x         }) σ ps in
  mk-data-info
    (renamectxt-rep ρ X)
    (renamectxt-rep ρ Xₒ)
    (substh Γ ρ σ -arg_ <$> asₚ)
    (substh Γ ρ σ -tT_ <$> asᵢ)
    ps
    (substh Γ' ρ' σ' kᵢ)
    (substh Γ' ρ' σ' k)
    (map-snd (substh Γ' ρ' σ') <$> cs)
    (map-snd (substh Γ ρ σ) <$> csₚₛ)
    gds
    eds


substh-arg Γ ρ σ = substh Γ ρ σ -arg_

substh-args Γ ρ σ = substh-arg Γ ρ σ <$>_

substh-params' Γ ρ σ ((Param me x tk) :: ps) =
  map-fst (Param me x (substh Γ ρ σ -tk tk) ::_)
    (substh-params' Γ (renamectxt-insert ρ x x) (trie-remove σ x) ps)
substh-params' Γ ρ σ [] = [] , Γ , ρ , σ

substh-params Γ ρ σ ps = fst (substh-params' Γ ρ σ ps)

substh-indices Γ ρ σ = params-to-indices ∘' substh-params Γ ρ σ ∘' indices-to-params

substh-case Γ ρ σ (Case x as t asₜₚ) =
  case (substh-case-args Γ ρ σ as) of λ where
    (as' , ρ' , Γ' , σ') →
      Case x as' (substh Γ' ρ' σ' t) (substh Γ' ρ' σ' -tT_ <$> asₜₚ)

substh-cases Γ ρ σ = map (substh-case Γ ρ σ)
    
substh-case-args Γ ρ σ as = foldr (λ where
  (CaseArg e x tk) f ρ Γ σ →
    let x' = subst-rename-var-if Γ ρ x σ (Var x) in
    map-fst (CaseArg e x' (substh Γ ρ σ -tk_ <$> tk) ::_)
            (f (renamectxt-insert ρ x x') (ctxt-var-decl x' Γ) (trie-remove σ x)))
  (λ ρ Γ σ → [] , ρ , Γ , σ) as ρ Γ σ


subst-ret-t : Set → Set
subst-ret-t T = {ed : exprd} → ctxt → ⟦ ed ⟧ → var → T → T

subst : ∀ {ed} → subst-ret-t ⟦ ed ⟧
subst Γ t x = substh Γ empty-renamectxt (trie-single x (, t))

subst-cases : subst-ret-t cases
subst-cases Γ t x = substh-cases Γ empty-renamectxt (trie-single x (, t))

subst-params : subst-ret-t params
subst-params Γ t x = substh-params Γ empty-renamectxt (trie-single x (, t))

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
  subst-params-args' (Param me x tk :: ps) (Arg t :: as) σ =
    subst-params-args' ps as (trie-insert σ x (, t))
  subst-params-args' (Param me x tk :: ps) (ArgE (inj₁ t) :: as) σ =
    subst-params-args' ps as (trie-insert σ x (, t))
  subst-params-args' (Param me x tk :: ps) (ArgE (inj₂ T) :: as) σ =
    subst-params-args' ps as (trie-insert σ x (, T))
  subst-params-args' ps as σ = σ , ps , as

subst-params-args' : ctxt → params → args → ∀ {ed} → ⟦ ed ⟧ → ⟦ ed ⟧ × params × args
subst-params-args' Γ ps as t = map-fst (λ σ → substs Γ σ t) (subst-params-args ps as)

infixr 3 [_-_/_]_
[_-_/_]_ : ∀ {ed ed'} → ctxt → ⟦ ed ⟧ → var → ⟦ ed' ⟧ → ⟦ ed' ⟧
[ Γ - t / x ] t' = subst Γ t x t'

subst-unqual : ∀ {ed} → ctxt → 𝕃 (posinfo × var) → ⟦ ed ⟧ → ⟦ ed ⟧
subst-unqual Γ xs t =
  subst-renamectxt
    Γ
    (foldr (uncurry λ pi x xs → renamectxt-insert xs (pi % x) x) empty-renamectxt xs)
    t

-- Given the parameters (32@x : ...) (41@y : ...32@x...),
-- returns (x : ...) (y : ...x...) × (32@x → x, 41@y → y)
unqual-params : ctxt → params → params × renamectxt
unqual-params = h empty-renamectxt where
  h : renamectxt → ctxt → params → params × renamectxt
  h ρ Γ [] = [] , ρ
  h ρ Γ (Param me qx atk :: ps) =
    let x = unqual-local qx in
    map-fst (Param me x (subst-renamectxt Γ ρ -tk atk) ::_)
      (h (renamectxt-insert ρ qx x) (ctxt-var-decl x Γ) ps)
