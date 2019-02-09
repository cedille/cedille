module rewriting where

open import lib

open import cedille-types
open import conversion
open import ctxt
open import general-util
open import is-free
open import lift
open import rename
open import subst
open import syntax-util
open import erase

private
  
  mk-phi : var → (eq t t' : term) → term
  mk-phi x eq t t' =
    Phi posinfo-gen
      (Rho posinfo-gen RhoPlain NoNums (Sigma posinfo-gen eq)
        (Guide posinfo-gen x (TpEq posinfo-gen t t' posinfo-gen))
        (Beta posinfo-gen (SomeTerm t posinfo-gen) (SomeTerm id-term posinfo-gen)))
      t t' posinfo-gen 

  head-types-match : ctxt → trie term → (complete partial : type) → 𝔹
  head-types-match Γ σ (TpApp T _) (TpApp T' _) = conv-type Γ T (substs Γ σ T')
  head-types-match Γ σ (TpAppt T _) (TpAppt T' _) = conv-type Γ T (substs Γ σ T')
  head-types-match Γ σ T T' = tt

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

rewriteC : ∀ {A : Set} → rewrite-t (rewrite-t A) → rewrite-t A
rewriteC r Γ op on eq t₁ t₂ n with r Γ op on eq t₁ t₂ n
...| r' , n' , sn with r' Γ op on eq t₁ t₂ sn
...| a , n'' , sn' = a , n' + n'' , sn'

rewriteR : ∀ {A : Set} → A → rewrite-t A
rewriteR a Γ op on eq t₁ t₂ n = a , 0 , n

{-# TERMINATING #-}
rewrite-term        : term        → rewrite-t term
rewrite-terma       : term        → rewrite-t term
rewrite-termh       : term        → rewrite-t term
rewrite-type        : type        → rewrite-t type
rewrite-typeh       : type        → rewrite-t type
rewrite-kind        : kind        → rewrite-t kind
rewrite-tk          : tk          → rewrite-t tk
rewrite-liftingType : liftingType → rewrite-t liftingType
rewrite-case : maybe (var × var)  → case   → rewrite-t case

rewrite-rename-var : ∀ {A} → var → (var → rewrite-t A) → rewrite-t A
rewrite-rename-var x r Γ op on eq t₁ t₂ n =
  let x' = rename-var-if Γ (renamectxt-insert empty-renamectxt t₂ t₂) x t₁ in
  r x' Γ op on eq t₁ t₂ n

rewrite-abs : ∀ {ed} → var → var → (⟦ ed ⟧ → rewrite-t ⟦ ed ⟧) → ⟦ ed ⟧ → rewrite-t ⟦ ed ⟧
rewrite-abs x x' g a Γ = let Γ = ctxt-var-decl x' Γ in g (rename-var Γ x x' a) Γ

rewrite-term t Γ op on eq t₁ t₂ sn =
  case rewrite-terma (erase-term t) Γ op on eq t₁ t₂ sn of λ where
    (t' , 0 , sn') → t , 0 , sn'
    (t' , n , sn') → mk-phi t₂ eq t t' , n , sn'

rewrite-terma t Γ op on eq t₁ t₂ sn =
  case conv-term Γ t t₁ of λ where
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
rewrite-termh (Lam pi NotErased pi' y NoClass t) =
  rewrite-rename-var y λ y' → rewriteR (Lam pi NotErased pi' y' NoClass) ≫rewrite
  rewrite-abs y y' rewrite-terma t
rewrite-termh (Var pi x) = rewriteR (Var pi x)
rewrite-termh (Let pi₁ fe (DefTerm pi₂ x NoType t) t') Γ = rewrite-terma (subst Γ t x t') Γ
--  rewrite-rename-var x λ x' → rewriteR (Let pi₁) ≫rewrite
--  (rewriteR (DefTerm pi₂ x' NoType) ≫rewrite rewrite-terma t) ≫rewrite
--  rewrite-abs x x' rewrite-terma t'
-- ^^^ Need to DEFINE "x" as "hnf Γ unfold-head t tt", not just declare it!
--     We may instead simply rewrite t' after substituting t for x
rewrite-termh (Mu  pi₁ pi₂ x t NoType pi₃ ms pi₄) =
  rewrite-rename-var x λ x' →
  rewriteR (Mu pi₁ pi₂ x') ≫rewrite
  rewrite-terma t ≫rewrite
  rewriteR NoType ≫rewrite
  rewriteR pi₃ ≫rewrite
  foldr (λ c r → rewriteR _::_ ≫rewrite rewrite-case (just $ x , x') c ≫rewrite r)
    (rewriteR []) ms ≫rewrite
  rewriteR pi₄
rewrite-termh (Mu' pi₁ NoTerm t NoType pi₂ ms pi₃) =
  rewriteR (Mu' pi₁ NoTerm) ≫rewrite
  rewrite-terma t ≫rewrite
  rewriteR NoType ≫rewrite
  rewriteR pi₂ ≫rewrite
  foldr (λ c r → rewriteR _::_ ≫rewrite rewrite-case nothing c ≫rewrite r)
    (rewriteR []) ms ≫rewrite
  rewriteR pi₃
rewrite-termh = rewriteR

rewrite-case xᵣ? (Case pi x cas t) =
  let f = maybe-else' xᵣ? id (uncurry rewrite-abs) rewrite-terma in
  rewriteR (uncurry $ Case pi x) ≫rewrite
  foldr {B = rewrite-t caseArgs → (term → rewrite-t term) → rewrite-t (caseArgs × term)}
    (λ {(CaseTermArg pi NotErased x) r cas fₜ →
      r (rewrite-rename-var x λ x' → rewriteR _::_ ≫rewrite rewriteR (CaseTermArg pi NotErased x') ≫rewrite cas) (λ t → rewrite-rename-var x λ x' → rewrite-abs x x' fₜ t); _ → id})
    (λ cas fₜ → rewriteR _,_ ≫rewrite cas ≫rewrite fₜ t) cas (rewriteR []) f

rewrite-type T Γ tt on eq t₁ t₂ sn
  with rewrite-typeh (hnf Γ unfold-head-no-lift T tt) Γ tt on eq t₁ t₂ sn
...| T' , 0 , sn' = T  , 0 , sn'
...| T' , n , sn' = T' , n , sn'
rewrite-type = rewrite-typeh

rewrite-typeh (Abs pi b pi' x atk T) =
  rewrite-rename-var x λ x' → 
  rewriteR (Abs pi b pi' x') ≫rewrite rewrite-tk atk ≫rewrite
  rewrite-abs x x' rewrite-type T
rewrite-typeh (Iota pi pi' x T T') =
  rewrite-rename-var x λ x' →
  rewriteR (Iota pi pi' x') ≫rewrite rewrite-type T ≫rewrite
  rewrite-abs x x' rewrite-type T'
rewrite-typeh (Lft pi pi' x t l) =
  rewrite-rename-var x λ x' →
  rewriteR (Lft pi pi' x') ≫rewrite
  rewrite-abs x x' rewrite-term t ≫rewrite
  rewrite-liftingType l
rewrite-typeh (TpApp T T') =
  rewriteR TpApp ≫rewrite rewrite-typeh T ≫rewrite rewrite-type T'
rewrite-typeh (TpAppt T t) =
  rewriteR TpAppt ≫rewrite rewrite-typeh T ≫rewrite rewrite-term t
rewrite-typeh (TpEq pi t₁ t₂ pi') =
  rewriteR (TpEq pi) ≫rewrite (rewriteR erase ≫rewrite rewrite-term t₁) ≫rewrite
  (rewriteR erase ≫rewrite rewrite-term t₂) ≫rewrite rewriteR pi'
rewrite-typeh (TpLambda pi pi' x atk T) =
  rewrite-rename-var x λ x' →
  rewriteR (TpLambda pi pi' x') ≫rewrite rewrite-tk atk ≫rewrite
  rewrite-abs x x' rewrite-type T
rewrite-typeh (TpArrow T a T') =
  rewriteR TpArrow ≫rewrite rewrite-type T ≫rewrite rewriteR a ≫rewrite rewrite-type T'
rewrite-typeh (TpLet pi (DefTerm pi' x T t) T') Γ =
  rewrite-type (subst Γ (Chi posinfo-gen T t) x T') Γ
rewrite-typeh (TpLet pi (DefType pi' x k T) T') Γ =
  rewrite-type (subst Γ T x T') Γ
rewrite-typeh (TpParens _ T _) = rewrite-type T
rewrite-typeh (NoSpans T _) = rewrite-type T
rewrite-typeh (TpHole pi) = rewriteR (TpHole pi)
rewrite-typeh (TpVar pi x) = rewriteR (TpVar pi x)

-- If we ever implement kind-level rewriting, we will need to go through
-- all the types of kind pi binding a term or type-to-kind arrow
-- if the right-hand side variable is free in the types of the bound variable,
-- and substitute each occurence of the term variable (eta-expanding if necessary)
-- in the body of the type with itself surrounded by a rewrite back the original
-- expected type (unless we lifted a term, then it gets really tricky because
-- we may not want to rewrite back?).
rewrite-kind = rewriteR
rewrite-liftingType = rewriteR

rewrite-tk (Tkt T) = rewriteR Tkt ≫rewrite rewrite-type T
rewrite-tk (Tkk k) = rewriteR Tkk ≫rewrite rewrite-kind k

post-rewrite-binder-type : ∀ {ed} → ctxt → var → term → (var → tk → ctxt → ctxt) → var → ⟦ ed ⟧ → type → ⟦ ed ⟧
post-rewrite-binder-type Γ x eq tk-decl x' Tₓ Tₓ' with is-free-in check-erased x Tₓ'
...| ff = Tₓ
...| tt = subst (tk-decl x' (Tkt Tₓ') Γ) (Rho posinfo-gen RhoPlain NoNums eq (Guide posinfo-gen x Tₓ') $ mvar x') x' Tₓ

post-rewrite-binder-kind : ∀ {ed} → ctxt → var → term → (var → tk → ctxt → ctxt) → var → ⟦ ed ⟧ → kind → ⟦ ed ⟧
post-rewrite-binder-kind Γ x eq tk-decl x' Tₓ kₓ' = Tₓ

post-rewrite-binder-tk : ∀ {ed} → ctxt → var → term → (var → tk → ctxt → ctxt) → var → ⟦ ed ⟧ → tk → ⟦ ed ⟧
post-rewrite-binder-tk Γ x eq tk-decl x' Tₓ (Tkt Tₓ') =
  post-rewrite-binder-type Γ x eq tk-decl x' Tₓ Tₓ'
post-rewrite-binder-tk Γ x eq tk-decl x' Tₓ (Tkk kₓ') =
  post-rewrite-binder-kind Γ x eq tk-decl x' Tₓ kₓ'

post-rewriteh : ctxt → var → term → (ctxt → var → term → tk → tk) → (var → tk → ctxt → ctxt) → type → type × kind

post-rewriteh Γ x eq prtk tk-decl (Abs pi b pi' x' atk T) =
  let atk = prtk Γ x eq atk
      T = fst $ post-rewriteh (tk-decl x' atk Γ) x eq prtk tk-decl T
      T = post-rewrite-binder-tk Γ x eq tk-decl x' T atk in
  Abs pi b pi' x' atk T , star
post-rewriteh Γ x eq prtk tk-decl (Iota pi pi' x' T T') =
  let T = fst $ post-rewriteh Γ x eq prtk tk-decl T
      T' = fst $ post-rewriteh (tk-decl x' (Tkt T) Γ) x eq prtk tk-decl T'
      T' = post-rewrite-binder-type Γ x eq tk-decl x' T' T in
  Iota pi pi' x' T T' , star
post-rewriteh Γ x eq prtk tk-decl (Lft pi pi' x' t lT) =
  Lft pi pi' x' t lT , liftingType-to-kind lT
post-rewriteh Γ x eq prtk tk-decl (TpApp T T') =
  elim-pair (post-rewriteh Γ x eq prtk tk-decl T') λ T' k' →
  elim-pair (post-rewriteh Γ x eq prtk tk-decl T) λ where
    T (KndPi pi pi' x' atk k) → TpApp T T' , hnf Γ unfold-head-no-lift (subst Γ T' x' k) tt
    T (KndArrow k k'') → TpApp T T' , hnf Γ unfold-head-no-lift k'' tt
    T k → TpApp T T' , k
post-rewriteh Γ x eq prtk tk-decl (TpAppt T t) =
  let t2 T' = if is-free-in check-erased x T' then Rho posinfo-gen RhoPlain NoNums (Sigma posinfo-gen eq) (Guide posinfo-gen x T') t else t in
  elim-pair (post-rewriteh Γ x eq prtk tk-decl T) λ where
    T (KndPi pi pi' x' (Tkt T') k) →
      let t3 = t2 T' in TpAppt T t3 , hnf Γ unfold-head-no-lift (subst Γ t3 x' k) tt
    T (KndTpArrow T' k) → TpAppt T (t2 T') , hnf Γ unfold-head-no-lift k tt
    T k → TpAppt T t , k
post-rewriteh Γ x eq prtk tk-decl (TpArrow T a T') = TpArrow (fst (post-rewriteh Γ x eq prtk tk-decl T)) a (fst (post-rewriteh Γ x eq prtk tk-decl T')) , star
post-rewriteh Γ x eq prtk tk-decl (TpLambda pi pi' x' atk T) =
  let atk = prtk Γ x eq atk in
  elim-pair (post-rewriteh (tk-decl x' atk Γ) x eq prtk tk-decl T) λ T k →
  let T = post-rewrite-binder-tk Γ x eq tk-decl x' T atk
      k = post-rewrite-binder-tk Γ x eq tk-decl x' k atk in
  TpLambda pi pi' x' atk T , KndPi pi pi' x' atk k
post-rewriteh Γ x eq prtk tk-decl (TpParens pi T pi') = post-rewriteh Γ x eq prtk tk-decl T
post-rewriteh Γ x eq prtk tk-decl (TpVar pi x') with env-lookup Γ x'
...| just (type-decl k , _) = mtpvar x' , hnf Γ unfold-head-no-lift k tt
...| just (type-def mps _ T k , _) = mtpvar x' , (hnf Γ unfold-head-no-lift (maybe-else id abs-expand-kind mps k) tt)
--...| just (datatype-def mps _ k _ , _) = mtpvar x' , hnf Γ unfold-head-no-lift (maybe-else id abs-expand-kind mps k) tt
--...| just (mu-def mps X k , _) = mtpvar x' , hnf Γ unfold-head-no-lift (maybe-else id abs-expand-kind mps k) tt
...| _ = mtpvar x' , star
post-rewriteh Γ x eq prtk tk-decl T = T , star

{-# TERMINATING #-}
post-rewrite : ctxt → var → (eq t₂ : term) → type → type
post-rewrite Γ x eq t₂ T = subst Γ t₂ x (fst (post-rewriteh Γ x eq prtk tk-decl T)) where
  prtk : ctxt → var → term → tk → tk
  tk-decl : var → tk → ctxt → ctxt
  prtk Γ x t (Tkt T) = Tkt (fst (post-rewriteh Γ x t prtk tk-decl T))
  prtk Γ x t (Tkk k) = Tkk (hnf Γ unfold-head-no-lift k tt)
  tk-decl x atk (mk-ctxt mod ss is os Δ) =
    mk-ctxt mod ss (trie-insert is x (h atk , "" , "")) os Δ where
    h : tk → ctxt-info
    h (Tkt T) = term-decl T
    h (Tkk k) = type-decl k

-- Functions for substituting the type T in ρ e @ x . T - t
{-# TERMINATING #-}
rewrite-at : ctxt → var → maybe term → 𝔹 → type → type → type
rewrite-ath : ctxt → var → maybe term → 𝔹 → type → type → type
rewrite-at-tk : ctxt → var → maybe term → 𝔹 → tk → tk → tk

rewrite-at-tk Γ x eq b (Tkt T) (Tkt T') = Tkt (rewrite-at Γ x eq b T T')
rewrite-at-tk Γ x eq b atk atk' = atk

rewrite-at Γ x eq b T T' =
  if ~ is-free-in tt x T'
    then T
    else if b && ~ head-types-match Γ (trie-single x (Hole posinfo-gen)) T T'
      then rewrite-ath Γ x eq ff (hnf Γ unfold-head-no-lift T tt) (hnf Γ unfold-head-no-lift T' tt)
      else rewrite-ath Γ x eq b T T'

rewrite-ath Γ x eq b (Abs pi1 b1 pi1' x1 atk1 T1) (Abs pi2 b2 pi2' x2 atk2 T2) =
  Abs pi1 b1 pi1' x1 (rewrite-at-tk Γ x eq tt atk1 atk2) (rewrite-at (ctxt-var-decl x1 Γ) x eq b T1 (rename-var Γ x2 x1 T2))
rewrite-ath Γ x eq b (Iota pi1 pi1' x1 T1 T1') (Iota pi2 pi2' x2 T2 T2') =
  Iota pi1 pi1' x1 (rewrite-at Γ x eq tt T1 T2) (rewrite-at (ctxt-var-decl x1 Γ) x eq b T1' (rename-var Γ x2 x1 T2'))
rewrite-ath Γ x eq b (Lft pi1 pi1' x1 t1 lT1) (Lft pi2 pi2' x2 t2 lT2) =
  Lft pi1 pi1' x1 (maybe-else' (maybe-if (is-free-in tt x (mlam x2 t2)) ≫maybe eq) t1 λ eq → mk-phi x eq t1 t2) lT1
rewrite-ath Γ x eq b (TpApp T1 T1') (TpApp T2 T2') =
  TpApp (rewrite-at Γ x eq b T1 T2) (rewrite-at Γ x eq b T1' T2')
rewrite-ath Γ x eq b (TpAppt T1 t1) (TpAppt T2 t2) =
  TpAppt (rewrite-at Γ x eq b T1 T2) (maybe-else' (maybe-if (is-free-in tt x t2) ≫maybe eq) t1 λ eq → mk-phi x eq t1 t2)
rewrite-ath Γ x eq b (TpArrow T1 a1 T1') (TpArrow T2 a2 T2') =
  TpArrow (rewrite-at Γ x eq tt T1 T2) a1 (rewrite-at Γ x eq tt T1' T2')
rewrite-ath Γ x eq b (TpEq pi1 t1 t1' pi1') (TpEq pi2 t2 t2' pi2') =
  TpEq pi1 t2 t2' pi1'
rewrite-ath Γ x eq b (TpLambda pi1 pi1' x1 atk1 T1) (TpLambda pi2 pi2' x2 atk2 T2) =
  TpLambda pi1 pi1' x1 (rewrite-at-tk Γ x eq tt atk1 atk2) (rewrite-at (ctxt-var-decl x1 Γ) x eq b T1 (rename-var Γ x2 x1 T2))
rewrite-ath Γ x eq b (TpLet pi1 (DefTerm pi1' x1 oc1 t1) T1) T2 = rewrite-at Γ x eq b (subst Γ t1 x1 T1) T2
rewrite-ath Γ x eq b T1 (TpLet pi2 (DefTerm pi2' x2 oc2 t2) T2) = rewrite-at Γ x eq b T1 (subst Γ t2 x2 T2)
rewrite-ath Γ x eq b (TpLet pi1 (DefType pi1' x1 k1 T1ₗ) T1) T2 = rewrite-at Γ x eq b (subst Γ T1ₗ x1 T1) T2
rewrite-ath Γ x eq b T1 (TpLet pi2 (DefType pi2' x2 k2 T2ₗ) T2) = rewrite-at Γ x eq b T1 (subst Γ T2ₗ x2 T2)
rewrite-ath Γ x eq b (TpVar pi1 x1) (TpVar pi2 x2) = TpVar pi1 x1
rewrite-ath Γ x eq b (TpHole pi1) (TpHole pi2) = TpHole pi1
rewrite-ath Γ x eq b (TpParens pi1 T1 pi1') T2 = rewrite-at Γ x eq b T1 T2
rewrite-ath Γ x eq b T1 (TpParens pi2 T2 pi2') = rewrite-at Γ x eq b T1 T2
rewrite-ath Γ x eq b (NoSpans T1 pi1) T2 = rewrite-at Γ x eq b T1 T2
rewrite-ath Γ x eq b T1 (NoSpans T2 pi2) = rewrite-at Γ x eq b T1 T2
rewrite-ath Γ x eq tt T1 T2 = rewrite-at Γ x eq ff (hnf Γ unfold-head-no-lift T1 tt) (hnf Γ unfold-head-no-lift T2 tt)
rewrite-ath Γ x eq ff T1 T2 = T1

hnf-ctr : ctxt → var → type → type
hnf-ctr Γ x T = rewrite-at Γ x nothing tt T $ hnf Γ (unfolding-elab unfold-all) T tt
