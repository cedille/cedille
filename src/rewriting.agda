module rewriting where

open import lib

open import cedille-types
open import conversion
open import ctxt
open import general-util
open import is-free
open import rename
open import subst
open import syntax-util

rewrite-t : Set → Set
rewrite-t T = ctxt → (is-plus : 𝔹) → (nums : maybe stringset) →
              (eq left : term) → (right : var) → (total-matches : ℕ) →
              T {- Returned value -} ×
              ℕ {- Number of rewrites actually performed -} ×
              ℕ {- Total number of matches, including skipped ones -}

infixl 4 _≫rewrite_

_≫rewrite_ : ∀ {A B : Set} → rewrite-t (A → B) → rewrite-t A → rewrite-t B
(f ≫rewrite a) Γ op on eq t₁ t₂ n with f Γ op on eq t₁ t₂ n
...| f' , n' , sn with a Γ op on eq t₁ t₂ sn
...| b , n'' , sn' = f' b , n' + n'' , sn'

rewriteR : ∀ {A : Set} → A → rewrite-t A
rewriteR a Γ op on eq t₁ t₂ n = a , 0 , n

{-# TERMINATING #-}
rewrite-term : term → rewrite-t term
rewrite-terma : term → rewrite-t term
rewrite-termh : term → rewrite-t term
rewrite-type : type → rewrite-t type
rewrite-kind : kind → rewrite-t kind
rewrite-tk : tk → rewrite-t tk
rewrite-liftingType : liftingType → rewrite-t liftingType

rewrite-rename-var : ∀ {A} → var → (var → rewrite-t A) → rewrite-t A
rewrite-rename-var x r Γ op on eq t₁ t₂ n =
  let x' = rename-var-if Γ (renamectxt-insert empty-renamectxt t₂ t₂) x t₁ in
  r x' Γ op on eq t₁ t₂ n

rewrite-abs : ∀ {A} → (ctxt → var → var → 𝔹 → A → A) → var → var → 𝔹 → (A → rewrite-t A) → A → rewrite-t A
rewrite-abs f x x' b g a Γ = let Γ = ctxt-var-decl posinfo-gen x' Γ in g (f Γ x x' b a) Γ
rewrite-term-abs = rewrite-abs rename-term
rewrite-type-abs = rewrite-abs rename-type
rewrite-kind-abs = rewrite-abs rename-kind

rewrite-term t Γ op on eq t₁ t₂ sn with rewrite-terma (erase-term t) Γ op on eq t₁ t₂ sn
...| t' , 0 , sn' = t , 0 , sn'
...| t' , n , sn' = Phi posinfo-gen
  (Rho posinfo-gen RhoPlain NoNums eq
    (Guide posinfo-gen t₂ (TpEq posinfo-gen t t' posinfo-gen))
    (Beta posinfo-gen NoTerm NoTerm))
  t t' posinfo-gen , n , sn'

rewrite-terma t Γ op on eq t₁ t₂ sn =
  case conv-term Γ t₁ t of λ where
  tt → case on of λ where
    (just ns) → case trie-contains ns (ℕ-to-string (suc sn)) of λ where
      tt → Var posinfo-gen t₂ , 1 , suc sn -- ρ nums contains n
      ff → t , 0 , suc sn -- ρ nums does not contain n
    nothing → Var posinfo-gen t₂ , 1 , suc sn
  ff → case op of λ where
    tt → case rewrite-termh (hnf Γ unfold-head t tt) Γ op on eq t₁ t₂ sn of λ where
      (t' , 0 , sn') → t , 0 , sn' -- if no rewrites were performed, return the pre-hnf t
      (t' , n' , sn') → t' , n' , sn'
    ff → rewrite-termh t Γ op on eq t₁ t₂ sn

rewrite-termh (App t e t') =
  rewriteR App ≫rewrite rewrite-terma t ≫rewrite rewriteR e ≫rewrite rewrite-terma t'
rewrite-termh (Lam pi KeptLambda pi' y NoClass t) =
  rewrite-rename-var y λ y' → rewriteR (Lam pi KeptLambda pi' y' NoClass) ≫rewrite
  rewrite-term-abs y y' tt rewrite-terma t
rewrite-termh (Var pi x) = rewriteR (Var pi x)
rewrite-termh = rewriteR

rewrite-type (Abs pi b pi' x atk T) =
  rewrite-rename-var x λ x' → 
  rewriteR (Abs pi b pi' x') ≫rewrite rewrite-tk atk ≫rewrite
  rewrite-type-abs x x' (tk-is-type atk) rewrite-type T
rewrite-type (Iota pi pi' x T T') =
  rewrite-rename-var x λ x' →
  rewriteR (Iota pi pi' x') ≫rewrite rewrite-type T ≫rewrite
  rewrite-type-abs x x' tt rewrite-type T'
rewrite-type (Lft pi pi' x t l) =
  rewrite-rename-var x λ x' →
  rewriteR (Lft pi pi' x') ≫rewrite
  rewrite-term-abs x x' ff rewrite-term t ≫rewrite
  rewrite-liftingType l
rewrite-type (TpApp T T') =
  rewriteR TpApp ≫rewrite rewrite-type T ≫rewrite rewrite-type T'
rewrite-type (TpAppt T t) =
  rewriteR TpAppt ≫rewrite rewrite-type T ≫rewrite rewrite-term t
rewrite-type (TpEq pi t₁ t₂ pi') =
  rewriteR (TpEq pi) ≫rewrite rewrite-term t₁ ≫rewrite
  rewrite-term t₂ ≫rewrite rewriteR pi'
rewrite-type (TpLambda pi pi' x atk T) =
  rewrite-rename-var x λ x' →
  rewriteR (TpLambda pi pi' x') ≫rewrite rewrite-tk atk ≫rewrite
  rewrite-type-abs x x' (tk-is-type atk) rewrite-type T
rewrite-type (TpArrow T a T') =
  rewriteR TpArrow ≫rewrite rewrite-type T ≫rewrite rewriteR a ≫rewrite rewrite-type T'
rewrite-type (TpParens _ T _) = rewrite-type T
rewrite-type (NoSpans T _) = rewrite-type T
rewrite-type (TpVar pi x) = rewriteR (TpVar pi x)
rewrite-type = rewriteR

rewrite-kind = rewriteR -- Unimplemented

rewrite-liftingType = rewriteR -- Unimplemented

rewrite-tk (Tkt T) = rewriteR Tkt ≫rewrite rewrite-type T
rewrite-tk (Tkk k) = rewriteR Tkk ≫rewrite rewrite-kind k


post-rewriteh : ctxt → var → term → (ctxt → var → term → tk → tk) → (var → tk → ctxt → ctxt) → type → type × kind

post-rewriteh Γ x eq prtk tk-decl (Abs pi b pi' x' atk T) =
  let atk' = prtk Γ x eq atk in
  Abs pi b pi' x' atk' (fst (post-rewriteh (tk-decl x' atk' Γ) x eq prtk tk-decl T)) , star
post-rewriteh Γ x eq prtk tk-decl (Iota pi pi' x' T T') =
  let T = fst (post-rewriteh Γ x eq prtk tk-decl T) in
  Iota pi pi' x' T (fst (post-rewriteh (tk-decl x' (Tkt T) Γ) x eq prtk tk-decl T')) , star
post-rewriteh Γ x eq prtk tk-decl (TpApp T T') =
  flip uncurry (post-rewriteh Γ x eq prtk tk-decl T) λ where
    T (KndPi pi pi' x' atk k) →
      flip uncurry (post-rewriteh Γ x eq prtk tk-decl T') λ T' k' →
      TpApp T T' , subst-kind Γ T' x' k
    T (KndArrow k k') → TpApp T T' , k
    T k → mtpvar "error in type-to-type application" , star
post-rewriteh Γ x eq prtk tk-decl (TpAppt T t) =
  flip uncurry (post-rewriteh Γ x eq prtk tk-decl T) λ where
    T (KndPi pi pi' x' (Tkt T') k) →
      if is-free-in tt x T'
        then TpAppt T (Rho posinfo-gen RhoPlain NoNums eq (Guide posinfo-gen x T') t) , subst-kind Γ t x' k
        else TpAppt T t , subst-kind Γ t x' k
    T (KndTpArrow T' k) → TpAppt T t , k
    T k → mtpvar "error in type-to-term application" , star
post-rewriteh Γ x eq prtk tk-decl (TpArrow T a T') = TpArrow (fst (post-rewriteh Γ x eq prtk tk-decl T)) a (fst (post-rewriteh Γ x eq prtk tk-decl T')) , star
post-rewriteh Γ x eq prtk tk-decl (TpLambda pi pi' x' atk T) =
  let atk' = prtk Γ x eq atk in
  flip uncurry (post-rewriteh (tk-decl x' atk' Γ) x eq prtk tk-decl T) λ T k →
  TpLambda pi pi' x' atk' T , KndPi pi pi' x' atk' k
post-rewriteh Γ x eq prtk tk-decl (TpParens pi T pi') = post-rewriteh Γ x eq prtk tk-decl T
post-rewriteh Γ x eq prtk tk-decl (TpVar pi x') with env-lookup Γ x'
...| just (type-decl k , _) = mtpvar x' , k
...| just (type-def ps T k , _) = mtpvar x' , k
...| _ = mtpvar ("error looking up variable " ^ x') , star
post-rewriteh Γ x eq prtk tk-decl T = T , star

{-# TERMINATING #-}
post-rewrite : ctxt → var → (eq t₂ : term) → type → type
post-rewrite Γ x eq t₂ T = subst-type Γ t₂ x (fst (post-rewriteh Γ x eq prtk tk-decl T)) where
  prtk : ctxt → var → term → tk → tk
  tk-decl : var → tk → ctxt → ctxt
  prtk Γ x t (Tkt T) = Tkt (fst (post-rewriteh Γ x t prtk tk-decl T))
  prtk Γ x t (Tkk k) = Tkk k
  tk-decl x atk (mk-ctxt mod ss is os) =
    mk-ctxt mod ss (trie-insert is x (h atk , "" , "")) os where
    h : tk → ctxt-info
    h (Tkt T) = term-decl T
    h (Tkk k) = type-decl k
