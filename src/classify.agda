import cedille-options
open import general-util
module classify (options : cedille-options.options)
                {mF : Set → Set} ⦃ mFm : monad mF ⦄ (write-to-log : string → mF ⊤) where

open import cedille-types
open import constants
open import conversion
open import ctxt
open import datatype-util
open import elab-util options
open import free-vars
open import meta-vars options {mF} ⦃ mFm ⦄
open import rename
open import resugar
open import rewriting
open import spans options {mF} ⦃ mFm ⦄
open import subst
open import syntax-util
open import type-util
open import to-string options
open import untyped-spans options {mF} ⦃ mFm ⦄

span-error-t : Set
span-error-t = (string × 𝕃 tagged-val)

{-# TERMINATING #-}
check-term : ctxt → ex-tm → (T? : maybe type) → spanM (check-ret T? term)
check-type : ctxt → ex-tp → (k? : maybe kind) → spanM (check-ret k? type)
check-kind : ctxt → ex-kd → spanM kind
check-tpkd : ctxt → ex-tk → spanM tpkd
check-args : ctxt → ex-args → params → spanM args
check-let : ctxt → ex-def → erased? → posinfo → posinfo → spanM (ctxt × var × tagged-val × (∀ {ed : exprd} → ⟦ ed ⟧ → ⟦ ed ⟧) × (term → term))
check-mu : ctxt → posinfo → posinfo → var → ex-tm → maybe ex-tp → posinfo → ex-cases → posinfo → (T? : maybe type) → spanM (check-ret T? term)
check-sigma : ctxt → posinfo → maybe ex-tm → ex-tm → maybe ex-tp → posinfo → ex-cases → posinfo → (T? : maybe type) → spanM (check-ret T? term)
get-datatype-info-from-head-type : ctxt → var → 𝕃 tmtp → spanM (span-error-t ⊎ datatype-info)
check-sigma-evidence : ctxt → maybe ex-tm → var → 𝕃 tmtp → spanM (span-error-t ⊎ (term × (term → term) × datatype-info))

check-cases : ctxt → ex-cases → (Dₓ : var) → (ctrs : trie type) → renamectxt → (ctr-ps : args) → (drop-as : ℕ) → type → (ctxt → term → type → term) → (ctxt → type → kind → type) → spanM (cases × err-m)
check-case : ctxt → ex-case → (earlier : stringset) → (Dₓ : var) → (ctrs : trie (type × params × 𝕃 tmtp)) → renamectxt → (ctr-ps : args) → (drop-as : ℕ) → type → (ctxt → term → type → term) → (ctxt → type → kind → type) → spanM (case × trie (type × params × 𝕃 tmtp))
check-refinement : ctxt → type → kind → spanM (type × 𝕃 tagged-val × err-m)

synth-tmtp' : ∀ {b X} → ctxt → if b then ex-tm else ex-tp → (if b then term else type → if b then type else kind → spanM X) → spanM X
synth-tmtp' {tt} Γ t f = check-term Γ t nothing >>= uncurry f
synth-tmtp' {ff} Γ T f = check-type Γ T nothing >>= uncurry f

check-tmtp' : ∀ {b X} → ctxt → if b then ex-tm else ex-tp → if b then type else kind → (if b then term else type → spanM X) → spanM X
check-tmtp' {tt} Γ t T f = check-term Γ t (just T) >>= f
check-tmtp' {ff} Γ T k f = check-type Γ T (just k) >>= f

check-tpkd' : ∀ {b X} → ctxt → if b then ex-kd else ex-tk → (if b then kind else tpkd → spanM X) → spanM X
check-tpkd' {tt} Γ k f = check-kind Γ k >>= f
check-tpkd' {ff} Γ k f = check-tpkd Γ k >>= f

lambda-bound-conv? : ctxt → var → tpkd → tpkd → 𝕃 tagged-val → 𝕃 tagged-val × err-m
lambda-bound-conv? Γ x tk tk' ts with conv-tpkd Γ tk tk'
...| tt = ts , nothing
...| ff =
  (to-string-tag-tk "declared classifier" Γ tk' ::
   to-string-tag-tk "expected classifier" Γ tk :: ts) ,
  just "The classifier given for a λ-bound variable is not the one we expected"

id' = id

hnf-of : ∀ {X : Set} {ed} → ctxt → ⟦ ed ⟧ → (⟦ ed ⟧ → X) → X
hnf-of Γ t f = f (hnf Γ unfold-head-elab t)

-- "⊢" = "\vdash" or "\|-"
-- "⇒" = "\r="
-- "⇐" = "\l="
infixr 2 hnf-of id' check-tpkd' check-tmtp' synth-tmtp'
syntax synth-tmtp' Γ t (λ t~ → f) = Γ ⊢ t ↝ t~ ⇒ f
syntax check-tmtp' Γ t T f = Γ ⊢ t ⇐ T ↝ f
syntax check-tpkd' Γ k f = Γ ⊢ k ↝ f
syntax id' (λ x → f) = x / f -- Supposed to look like a horizontal bar (as in typing rules)
syntax hnf-of Γ t f = Γ ⊢ t =β= f


-- t [-]t'
check-term Γ (ExApp t e t') Tₑ? =
  check-term-spine Γ (ExApp t e t') (proto-maybe Tₑ?) tt
    on-fail return-when (Hole (term-start-pos t)) (TpHole (term-start-pos t))
    >>=m (uncurry return-when ∘ check-term-spine-elim Γ)
  where open import type-inf options {mF} check-term check-type

-- t ·T
check-term Γ (ExAppTp tₕ Tₐ) Tₑ? =
-- "Γ ⊢ tₕ ↝ tₕ~ ⇒ Tₕ~ /" desugars to "synth-tmtp' Γ tₕ λ tₕ~ Tₕ~ →"
  Γ ⊢ tₕ ↝ tₕ~ ⇒ Tₕ~ /
  Γ ⊢ Tₕ~ =β= λ where
    (TpAbs tt x (Tkk kₐ) Tᵣ) →
      Γ ⊢ Tₐ ⇐ kₐ ↝ Tₐ~ /
      let Tᵣ = [ Γ - Tₐ~ / x ] Tᵣ in
      [- AppTp-span tt (term-start-pos tₕ) (type-end-pos Tₐ) (maybe-to-checking Tₑ?)
           (head-type Γ Tₕ~ :: type-data Γ Tᵣ :: expected-type-if Γ Tₑ?)
           (check-for-type-mismatch-if Γ "synthesized" Tₑ? Tᵣ) -]
      return-when (AppTp tₕ~ Tₐ~) Tᵣ
    Tₕ'~ →
      untyped-type Γ Tₐ >>= λ Tₐ~ →
      [- AppTp-span tt (term-start-pos tₕ) (type-end-pos Tₐ) (maybe-to-checking Tₑ?)
           (head-type Γ Tₕ'~ :: arg-type Γ Tₐ~ :: expected-type-if Γ Tₑ?)
           (unless (is-hole Tₕ'~)
              ("The type synthesized from the head does not allow it to be applied" ^
               " to a type argument")) -]
      return-when (AppTp tₕ~ Tₐ~) (TpHole (term-start-pos tₕ))

-- β[<t?>][{t?'}]
check-term Γ (ExBeta pi t? t?') Tₑ? =
  maybe-map (λ {(PosTm t _) → untyped-term Γ t}) t?  >>=? λ t?~  →
  maybe-map (λ {(PosTm t _) → untyped-term Γ t}) t?' >>=? λ t?'~ →
  let t'~ = maybe-else' t?'~ id-term id
      e-t~ = maybe-else' Tₑ?
        (maybe-else' t?~
          (inj₁ ([] , "When synthesizing, specify what equality to prove with β<...>"))
          (λ t → inj₂ (t , nothing)))
        λ Tₑ → Γ ⊢ Tₑ =β= λ where
          (TpEq t₁ t₂) →
            if conv-term Γ t₁ t₂
              then maybe-else' (t?~ >>= λ t~ → check-for-type-mismatch Γ "computed"
                                    (TpEq t~ t~) (TpEq t₁ t₂) >>= λ e → just (e , t~))
                     (inj₂ (t₁ , just t₂))
                     (uncurry λ e t~ → inj₁ ([ type-data Γ (TpEq t~ t~) ] , e))
              else inj₁ ([] , "The two terms in the equation are not β-equal")
          Tₕ → inj₁ ([] , "The expected type is not an equation")
      e? = either-else' e-t~ (map-snd just) λ _ → [] , nothing
      fₓ = fresh-var Γ "x"
      t~T~ = either-else' e-t~ (λ _ → Hole pi , TpEq (Hole pi) (Hole pi))
             $ uncurry λ t₁ → maybe-else (Beta t₁ t'~ , TpEq t₁ t₁)
                                λ t₂ → (Beta t₁ t'~) , TpEq t₁ t₂ in
  [- uncurry (λ tvs → Beta-span pi (term-end-pos (ExBeta pi t? t?')) (maybe-to-checking Tₑ?)
         (expected-type-if Γ Tₑ? ++ tvs)) e? -]
  uncurry return-when t~T~

-- χ [T?] - t
check-term Γ (ExChi pi T? t) Tₑ? =
  (maybe-else' T?
    (check-term Γ t nothing)
    λ T → Γ ⊢ T ⇐ KdStar ↝ T~ /
          Γ ⊢ t ⇐ T~ ↝ t~ /
          return2 t~ T~
  ) >>= uncurry λ t~ T~ →
  [- Chi-span Γ pi (just T~) t (maybe-to-checking Tₑ?)
       (type-data Γ T~ :: expected-type-if Γ Tₑ?)
       (check-for-type-mismatch-if Γ
         (maybe-else' T? "synthesized" (const "computed")) Tₑ? T~) -]
  return-when t~ T~

-- δ [T?] - t
check-term Γ (ExDelta pi T? t) Tₑ? =
  Γ ⊢ t ↝ t~ ⇒ Tcontra /
  maybe-else' T?
    (return (maybe-else' Tₑ? (TpAbs Erased "X" (Tkk KdStar) (TpVar "X")) id))
    (λ T → Γ ⊢ T ⇐ KdStar ↝ return) >>= λ T~' →
  let b = Γ ⊢ Tcontra =β= λ {(TpEq t₁ t₂) → when (inconv Γ t₁ t₂) (t₁ , t₂); _ → nothing}
      b? = unless (conv-type Γ Tcontra (TpEq tt-term ff-term)) triv >> b in
  [- Delta-span pi t (maybe-to-checking Tₑ?)
      (to-string-tag "the contradiction" Γ Tcontra ::
       type-data Γ T~' :: expected-type-if Γ Tₑ?)
       (maybe-not b >> just
         "We could not find a contradiction in the synthesized type of the subterm") -]
  return-when (Delta b? T~' t~) T~'

-- ε[lr][-?] t
check-term Γ (ExEpsilon pi lr -? t) Tₑ? =
  let hnf-from = if -? then hanf Γ tt else hnf Γ unfold-head
      update-eq : term → term → type
      update-eq = λ t₁ t₂ → uncurry TpEq $ maybe-else' lr (hnf-from t₁ , hnf-from t₂) λ lr →
                    if lr then (t₁ , hnf-from t₂) else (hnf-from t₁ , t₂) in
  case-ret {m = Tₑ?}
    (Γ ⊢ t ↝ t~ ⇒ T~ /
     Γ ⊢ T~ =β= λ where
       (TpEq t₁ t₂) →
         let Tᵣ = update-eq t₁ t₂ in
         [- Epsilon-span pi lr -? t (maybe-to-checking Tₑ?) [ type-data Γ Tᵣ ] nothing -]
         return2 t~ Tᵣ
       Tₕ →
         [- Epsilon-span pi lr -? t (maybe-to-checking Tₑ?)
              [ to-string-tag "synthesized type" Γ Tₕ ]
              (unless (is-hole Tₕ)
                 "The synthesized type of the body is not an equation") -]
         return2 t~ Tₕ)
    λ Tₑ → Γ ⊢ Tₑ =β= λ where
      (TpEq t₁ t₂) →
        [- Epsilon-span pi lr -? t (maybe-to-checking Tₑ?)
             [ expected-type Γ (TpEq t₁ t₂) ] nothing -]
        Γ ⊢ t ⇐ update-eq t₁ t₂ ↝ return
      Tₕ →
        [- Epsilon-span pi lr -? t (maybe-to-checking Tₑ?) [ expected-type Γ Tₕ ]
             (unless (is-hole Tₕ) "The expected type is not an equation") -]
        untyped-term Γ t

-- ●
check-term Γ (ExHole pi) Tₑ? =
  [- hole-span Γ pi Tₑ? (maybe-to-checking Tₑ?) [] -]
  return-when (Hole pi) (TpHole pi)

-- [ t₁ , t₂ [@ Tₘ,?] ]
check-term Γ (ExIotaPair pi t₁ t₂ Tₘ? pi') Tₑ? =
  maybe-else' {B = spanM (err-m × 𝕃 tagged-val × term × term × term × type)} Tₑ?
    (maybe-else' Tₘ?
       (untyped-term Γ t₁ >>= λ t₁~ →
        untyped-term Γ t₂ >>= λ t₂~ →
        return (just "Iota pairs require a specified type when synthesizing" , [] ,
                t₁~ , t₁~ , t₂~ , TpHole pi))
       λ {(ExGuide pi'' x T₂) →
            Γ ⊢ t₁ ↝ t₁~ ⇒ T₁~ /
            (Γ , pi'' - x :` Tkt T₁~) ⊢ T₂ ⇐ KdStar ↝ T₂~ /
            Γ ⊢ t₂ ⇐ [ Γ - t₁~ / (pi'' % x) ] T₂~ ↝ t₂~ /
            let T₂~ = [ Γ - Var x / (pi'' % x) ] T₂~
                bd = binder-data Γ pi'' x (Tkt T₁~) ff nothing
                       (type-start-pos T₂) (type-end-pos T₂) in
            [- Var-span Γ pi'' x checking [ type-data Γ T₁~ ] nothing -]
            return (nothing , (type-data Γ (TpIota x T₁~ T₂~) :: [ bd ]) ,
                    IotaPair t₁~ t₂~ x T₂~ , t₁~ , t₂~ , TpIota x T₁~ T₂~)})
    (λ Tₑ → Γ ⊢ Tₑ =β= λ where
      (TpIota x T₁ T₂) →
        Γ ⊢ t₁ ⇐ T₁ ↝ t₁~ /
        maybe-else' Tₘ?
          (Γ ⊢ t₂ ⇐ [ Γ - t₁~ / x ] T₂ ↝ t₂~ /
           return (nothing , (type-data Γ (TpIota x T₁ T₂) :: [ expected-type Γ Tₑ ]) ,
                   IotaPair t₁~ t₂~ x T₂ , t₁~ , t₂~ , TpIota x T₁ T₂))
          λ {(ExGuide pi'' x' Tₘ) →
               (Γ , pi'' - x' :` Tkt T₁) ⊢ Tₘ ⇐ KdStar ↝ Tₘ~ /
               let Tₘ~ = [ Γ - Var x' / (pi'' % x') ] Tₘ~
                   T₂ = [ Γ - Var x' / x ] T₂
                   Tₛ = TpIota x' T₁ Tₘ~ in
               Γ ⊢ t₂ ⇐ [ Γ - t₁~ / x' ] Tₘ~ ↝ t₂~ /
               [- Var-span Γ pi'' x checking [ type-data Γ T₁ ] nothing -]
               return (check-for-type-mismatch Γ "computed" Tₘ~ T₂ ,
                       (type-data Γ Tₛ :: expected-type Γ (TpIota x' T₁ T₂) ::
                        [ binder-data Γ pi'' x' (Tkt T₁) ff nothing
                            (type-start-pos Tₘ) (type-end-pos Tₘ) ]) ,
                       IotaPair t₁~ t₂~ x' Tₘ~ , t₁~ , t₂~ , Tₛ)}
      Tₕ →
        untyped-term Γ t₁ >>= λ t₁~ →
        untyped-term Γ t₂ >>= λ t₂~ →
        return (unless (is-hole Tₕ) "The expected type is not an iota-type" ,
                [ expected-type Γ Tₕ ] , t₁~ , t₁~ , t₂~ , Tₕ)) >>= λ where
    (err? , tvs , t~ , t₁~ , t₂~ , T~) →
      let conv-e = "The two components of the iota-pair are not convertible (as required)"
          conv-e? = unless (conv-term Γ t₁~ t₂~) conv-e
          conv-tvs = maybe-else' conv-e? [] λ _ →
              to-string-tag "hnf of the first component"  Γ (hnf Γ unfold-head t₁~) ::
            [ to-string-tag "hnf of the second component" Γ (hnf Γ unfold-head t₂~) ] in
      [- IotaPair-span pi pi' (maybe-to-checking Tₑ?) (conv-tvs ++ tvs)
           (conv-e? ||-maybe err?) -]
      return-when t~ T~

-- t.(1 / 2)
check-term Γ (ExIotaProj t n pi) Tₑ? =
  Γ ⊢ t ↝ t~ ⇒ T~ /
  let n? = case n of λ {"1" → just ι1; "2" → just ι2; _ → nothing} in
  maybe-else' n?
    ([- IotaProj-span t pi (maybe-to-checking Tₑ?) (expected-type-if Γ Tₑ?)
          (just "Iota-projections must use .1 or .2 only") -]
     return-when t~ (TpHole pi)) λ n →
    Γ ⊢ T~ =β= λ where
      (TpIota x T₁ T₂) →
        let Tᵣ = if n iff ι1 then T₁ else ([ Γ - t~ / x ] T₂) in
        [- IotaProj-span t pi (maybe-to-checking Tₑ?)
             (type-data Γ Tᵣ :: expected-type-if Γ Tₑ?)
             (check-for-type-mismatch-if Γ "synthesized" Tₑ? Tᵣ) -]
        return-when (IotaProj t~ n) Tᵣ
      Tₕ~ →
        [- IotaProj-span t pi (maybe-to-checking Tₑ?)
             (head-type Γ Tₕ~ :: expected-type-if Γ Tₑ?)
             (unless (is-hole Tₕ~)
                "The synthesized type of the head is not an iota-type") -]
        return-when (IotaProj t~ n) (TpHole pi)

-- λ/Λ x [: T?]. t
check-term Γ (ExLam pi e pi' x tk? t) Tₑ? =
  [- punctuation-span "Lambda" pi (posinfo-plus pi 1) -]
  let erase-err : (exp act : erased?) → tpkd → term → err-m × 𝕃 tagged-val
      erase-err = λ where
        Erased NotErased tk t →
          just ("The expected type is a ∀-abstraction (implicit input), " ^
                "but the term is a λ-abstraction (explicit input)") , []
        NotErased Erased tk t →
          just ("The expected type is a Π-abstraction (explicit input), " ^
                "but the term is a Λ-abstraction (implicit input)") , []
        Erased Erased tk t →
          maybe-else (nothing , []) (λ e-tv → just (fst e-tv) , [ snd e-tv ])
            (trie-lookup (free-vars (erase t)) x >>
             just ("The Λ-bound variable occurs free in the erasure of the body" ,
                   erasure Γ t))
        NotErased NotErased (Tkk _) t →
          just "λ-terms must bind a term, not a type (use Λ instead)" , []
        NotErased NotErased (Tkt _) t →
          nothing , [] in
  case-ret {m = Tₑ?}
    (maybe-else' tk?
      (untyped-term (Γ , pi' - x :` Tkt (TpHole pi')) t >>= λ t~ →
       [- Lam-span Γ synthesizing pi pi' e x (Tkt (TpHole pi')) t []
           (just ("We are not checking this abstraction against a type, " ^
                  "so a classifier must be given for the bound variable " ^ x)) -]
       return2 (Lam e x nothing (rename-var Γ (pi' % x) x t~)) (TpHole pi'))
      λ tk →
        Γ ⊢ tk ↝ tk~ /
        (Γ , pi' - x :` tk~) ⊢ t ↝ t~ ⇒ T~ /
        let T~ = rename-var Γ (pi' % x) x T~
            t~ = rename-var Γ (pi' % x) x t~
            Tᵣ = TpAbs e x tk~ T~ in
        [- var-span e (Γ , pi' - x :` tk~) pi' x checking tk~ nothing -]
        [- uncurry (λ tvs → Lam-span Γ synthesizing pi pi' e x tk~ t
               (type-data Γ Tᵣ :: tvs)) (twist-× (erase-err e e tk~ t~)) -]
        return2 (Lam e x (just tk~) t~) Tᵣ)
    λ Tₑ → Γ ⊢ Tₑ =β= λ where
      (TpAbs e' x' tk T) →
        maybe-map (check-tpkd Γ) tk? >>=? tk~? /
        let tk~ = maybe-else' tk~? tk id in
        --maybe-else' tk? (return tk) (λ tk → Γ ⊢ tk ↝ return) >>= tk~ /
        (Γ , pi' - x :` tk~) ⊢ t ⇐ rename-var Γ x' (pi' % x) T ↝ t~ /
        let xₙ = if x =string ignored-var && is-free-in x' T then x' else x
            t~ = rename-var Γ (pi' % x) xₙ t~
            T = rename-var Γ x' xₙ T
            Tₛ = TpAbs e xₙ tk~ T
            Tₑ = TpAbs e' xₙ tk T
            vₑ = check-for-tpkd-mismatch-if Γ "computed" tk~? tk in
        [- var-span e (Γ , pi' - x :` tk~) pi' x (maybe-to-checking tk?) tk~ nothing -]
        [- uncurry (λ err tvs → Lam-span Γ checking pi pi' e x tk~ t
                 (type-data Γ Tₛ :: expected-type Γ Tₑ :: tvs) (err ||-maybe vₑ))
             (erase-err e' e tk~ t~) -]
        return (Lam e xₙ (just tk~) t~)
      Tₕ →
        maybe-else' tk? (return (Tkt (TpHole pi'))) (check-tpkd Γ) >>= tk~ /
        untyped-term (Γ , pi' - x :` tk~) t >>= t~ /
        [- Lam-span Γ checking pi pi' e x (Tkt (TpHole pi')) t
             [ expected-type Γ Tₕ ] (just "The expected type is not a ∀- or a Π-type") -]
        return (Lam e x (unless (is-hole -tk' tk~) tk~)
                 (rename-var Γ (pi' % x) x t~))

-- [d] - t
check-term Γ (ExLet pi e? d t) Tₑ? =
  check-let Γ d e? (term-start-pos t) (term-end-pos t) >>= λ where
    (Γ' , x , tv , σ , f) →
      case-ret-body {m = Tₑ?} (check-term Γ' t Tₑ?) λ t~ T~ →
      [- punctuation-span "Parens (let)" pi (term-end-pos t) -]
      [- Let-span e? pi (term-end-pos t) (maybe-to-checking Tₑ?)
           (maybe-else' Tₑ? (type-data Γ T~) (expected-type Γ) :: [ tv ])
           (when (e? && is-free-in x (erase t~))
              (unqual-local x ^ "occurs free in the body of the term")) -]
      return-when (f t~) (σ T~)


-- open/close x - t
check-term Γ (ExOpen pi o pi' x t) Tₑ? =
  let Γ? = ctxt-clarify-def Γ o x
      e? = maybe-not Γ? >> just (x ^ " does not have a definition that can be " ^
                                       (if o then "opened" else "closed")) in
  [- Var-span Γ pi' x (maybe-to-checking Tₑ?) [ not-for-navigation ] nothing -]
  [- Open-span o pi x t (maybe-to-checking Tₑ?) (expected-type-if Γ Tₑ?) e? -]
  check-term (maybe-else' Γ? Γ id) t Tₑ?

-- (t)
check-term Γ (ExParens pi t pi') Tₑ? =
  [- punctuation-span "Parens (term)" pi pi' -]
  check-term Γ t Tₑ?

-- φ t₌ - t₁ {t₂}
check-term Γ (ExPhi pi t₌ t₁ t₂ pi') Tₑ? =
  case-ret-body {m = Tₑ?} (check-term Γ t₁ Tₑ?) λ t₁~ T~ →
  untyped-term Γ t₂ >>= λ t₂~ →
  Γ ⊢ t₌ ⇐ TpEq t₁~ t₂~ ↝ t₌~ /
  [- Phi-span pi pi' (maybe-to-checking Tₑ?)
       [ maybe-else' Tₑ? (type-data Γ T~) (expected-type Γ)] nothing -]
  return-when (Phi t₌~ t₁~ t₂~) T~

-- ρ[+]<ns> t₌ [@ Tₘ?] - t
check-term Γ (ExRho pi ρ+ <ns> t₌ Tₘ? t) Tₑ? =
  Γ ⊢ t₌ ↝ t₌~ ⇒ T₌ /
  Γ ⊢ T₌ =β= λ where
    (TpEq t₁ t₂) →
      let tₗ = if isJust Tₑ? then t₁ else t₂
          tᵣ = if isJust Tₑ? then t₂ else t₁
          tvs = λ T~ Tᵣ → to-string-tag "equation" Γ (TpEq t₁ t₂) ::
                          maybe-else' Tₑ?
                            (to-string-tag "type of second subterm" Γ T~)
                            (expected-type Γ) ::
                          [ to-string-tag "rewritten type" Γ Tᵣ ] in
      maybe-else' Tₘ?
        (elim-pair (optNums-to-stringset <ns>) λ ns ns-e? →
         let x = fresh-var Γ "x"
             Γ' = ctxt-var-decl x Γ
             T-f = λ T → rewrite-type T Γ' ρ+ ns (just t₌~) tₗ x 0
             Tᵣ-f = fst ∘ T-f
             nn-f = snd ∘ T-f
             Tₚ-f = map-fst (post-rewrite Γ' x t₌~ tᵣ) ∘ T-f in
         maybe-else' Tₑ?
           (Γ ⊢ t ↝ t~ ⇒ T~ /
            return2 t~ T~)
           (λ Tₑ → Γ ⊢ t ⇐ fst (Tₚ-f Tₑ) ↝ t~ /
             return2 t~ Tₑ) >>=c λ t~ T~ →
         elim-pair (Tₚ-f T~) λ Tₚ nn →
         [- Rho-span pi t₌ t (maybe-to-checking Tₑ?) ρ+
              (inj₁ (fst nn)) (tvs T~ Tₚ) (ns-e? (snd nn)) -]
         return-when (Rho t₌~ x (erase (Tᵣ-f T~)) t~) Tₚ)
        λ where
          (ExGuide pi' x Tₘ) →
            [- Var-span Γ pi' x untyped [] nothing -]
            let Γ' = Γ , pi' - x :` Tkt (TpHole pi') in
            untyped-type Γ' Tₘ >>= λ Tₘ~ →
            let Tₘ~ = [ Γ' - Var x / (pi' % x) ] Tₘ~
                T' = [ Γ' - tₗ / x ] Tₘ~
                T'' = post-rewrite Γ' x t₌~ tᵣ (rewrite-at Γ' x (just t₌~) tt T' Tₘ~)
                check-str = if isJust Tₑ? then "computed" else "synthesized" in
            maybe-else' Tₑ?
              (check-term Γ t nothing)
              (λ Tₑ → Γ ⊢ t ⇐ T'' ↝ t~ /
                return2 t~ Tₑ) >>=c λ t~ T~ →
            [- Rho-span pi t₌ t (maybe-to-checking Tₑ?) ρ+ (inj₂ x) (tvs T~ T'')
                 (check-for-type-mismatch Γ check-str T' T~) -]
            return-when (Rho t₌~ x Tₘ~ t~) T''
    Tₕ →
      Γ ⊢ t ↝ t~ ⇒ λ T~ →
      [- Rho-span pi t₌ t (maybe-to-checking Tₑ?) ρ+ (inj₁ 1)
           (to-string-tag "type of first subterm" Γ Tₕ ::
            [ to-string-tag "type of second subterm" Γ T~ ])
           (unless (is-hole Tₕ)
              "We could not synthesize an equation from the first subterm") -]
      return-when t~ T~

-- ς t
check-term Γ (ExVarSigma pi t) Tₑ? =
  case-ret
    (Γ ⊢ t ↝ t~ ⇒ T /
     Γ ⊢ T =β= λ where
       (TpEq t₁ t₂) →
         [- VarSigma-span pi t synthesizing [ type-data Γ (TpEq t₂ t₁) ] nothing -]
         return2 (VarSigma t~) (TpEq t₂ t₁)
       Tₕ →
         [- VarSigma-span pi t synthesizing [ type-data Γ Tₕ ]
           (unless (is-hole Tₕ)
              "The synthesized type of the body is not an equation") -]
         return2 (VarSigma t~) Tₕ)
  λ Tₑ →
    Γ ⊢ Tₑ =β= λ where
      (TpEq t₁ t₂) →
        Γ ⊢ t ⇐ TpEq t₂ t₁ ↝ t~ /
        [- VarSigma-span pi t checking [ expected-type Γ (TpEq t₁ t₂) ] nothing -]
        return (VarSigma t~)
      Tₕ →
        [- VarSigma-span pi t checking [ expected-type Γ Tₕ ]
             (unless (is-hole Tₕ)
                "The expected type is not an equation") -]
        untyped-term Γ t

-- θ t ts
check-term Γ (ExTheta pi θ t ts) Tₑ? =
  case-ret {m = Tₑ?}
    ([- Theta-span Γ pi θ t ts synthesizing [] (just
            "Theta-terms can only be used when checking (and we are synthesizing here)") -]
     return2 (Hole pi) (TpHole pi))
    λ Tₑ →
      Γ ⊢ t ↝ t~ ⇒ T /
      let x = case hnf Γ unfold-head t~ of λ {(Var x) → x; _ → "x"}
          x' = fresh-var Γ x in
      Γ ⊢ T =β= λ where
        (TpAbs me x (Tkk kd) tp) →
          (case θ of λ where
            (AbstractVars vs) → either-else' (wrap-vars vs Tₑ) (return2 (TpHole pi) ∘ just) λ Tₘ → return2 Tₘ nothing
            Abstract → return2 (TpLam x' (Tkt T) (rename-var Γ x x' Tₑ)) nothing
            AbstractEq → return2 (TpLam x' (Tkt T) (TpAbs Erased ignored-var (Tkt (TpEq t~ (Var x'))) (rename-var Γ x x' Tₑ))) nothing) >>=c λ Tₘ e₁ →
          check-refinement Γ Tₘ kd >>=c λ Tₘ → uncurry λ tvs e₂ →
          let tp' = [ Γ - Tₘ / x ] tp in
          check-lterms ts (AppTp t~ Tₘ) tp' >>=c λ t~ T~ →
          let e₃ = check-for-type-mismatch Γ "synthesized" T~ Tₑ
              t~ = case θ of λ {AbstractEq → AppEr t~ (Beta (erase t~) id-term); _ → t~} in
          [- Theta-span Γ pi θ t ts checking
               (type-data Γ T~ :: expected-type Γ Tₑ :: tvs)
               (e₁ ||-maybe (e₂ ||-maybe e₃)) -]
          return t~
        Tₕ →
          [- Theta-span Γ pi θ t ts checking (head-type Γ Tₕ :: expected-type Γ Tₑ :: [])
               (unless (is-hole Tₕ) "The synthesized type of the head is not a type-forall") -]
          return (Hole pi)
  where
  check-lterms : 𝕃 lterm → term → type → spanM (term × type)
  check-lterms [] tm tp = return2 tm tp
  check-lterms (Lterm me t :: ts) tm tp =
    Γ ⊢ tp =β= λ where
      (TpAbs me' x (Tkt T) T') →
        Γ ⊢ t ⇐ T ↝ t~ /
        (if me iff me' then return triv else spanM-add
          (Theta-span Γ pi θ t [] checking [] (just "Mismatched erasure of theta arg"))) >>
        check-lterms ts (if me then AppEr tm t~ else App tm t~) ([ Γ - t~ / x ] T')
      Tₕ →
        (if is-hole Tₕ then id
          else [- Theta-span Γ pi θ t [] checking [ expected-type Γ Tₕ ]
                    (just "The expected type is not an arrow type") -]_)
        (untyped-term Γ t >>= λ t~ → check-lterms ts (if me then AppEr tm t~ else App tm t~) Tₕ)

  var-not-in-scope : var → string
  var-not-in-scope x =
    "We could not compute a motive from the given term because " ^
    "the abstracted variable " ^ x ^ " is not in scope"
  
  wrap-var : var → type → string ⊎ type
  wrap-var x T =
    let x' = fresh-var Γ x in
    maybe-else' (ctxt-lookup-tpkd-var Γ x)
      (inj₁ (var-not-in-scope x))
      λ {(qx , as , tk) → inj₂ (TpLam x' tk (rename-var Γ qx x' T))}
  wrap-vars : 𝕃 var → type → var ⊎ type
  wrap-vars [] T = inj₂ T
  wrap-vars (x :: xs) T = wrap-vars xs T >>= wrap-var x

  motive : var → var → type → type → theta → term → type
  motive x x' T T' Abstract t = TpLam x' (Tkt T') (rename-var Γ x x' T)
  motive x x' T T' AbstractEq t = TpLam x' (Tkt T') (TpAbs Erased ignored-var (Tkt (TpEq t (Var x'))) (rename-var Γ x x' T))
  motive x x' T T' (AbstractVars vs) t = T -- Shouldn't happen


-- μ(' / rec.) t [@ Tₘ?] {ms...}
check-term Γ (ExMu pi1 pi2 x t Tₘ? pi' ms pi'') Tₑ? =
  check-mu Γ pi1 pi2 x t Tₘ? pi' ms pi'' Tₑ?

check-term Γ (ExSigma pi t? t Tₘ? pi' ms pi'') Tₑ? =
  check-sigma Γ pi t? t Tₘ? pi' ms pi'' Tₑ?

-- x
check-term Γ (ExVar pi x) Tₑ? =
  maybe-else' (ctxt-lookup-term-var Γ x)
    ([- Var-span Γ pi x (maybe-to-checking Tₑ?)
          (expected-type-if Γ Tₑ?)
          (just "Missing a type for a term variable") -]
     return-when (Var x) (TpHole pi))
    λ {(qx , as , T) →
      [- Var-span Γ pi x (maybe-to-checking Tₑ?)
           (type-data Γ T :: expected-type-if Γ Tₑ?)
           (check-for-type-mismatch-if Γ "computed" Tₑ? T) -]
      return-when (apps-term (Var qx) as) T}

-- ∀/Π x : tk. T
check-type Γ (ExTpAbs pi e pi' x tk T) kₑ? =
  Γ ⊢ tk ↝ tk~ /
  (Γ , pi' - x :` tk~) ⊢ T ⇐ KdStar ↝ T~ /
  let T~ = rename-var Γ (pi' % x) x T~ in
  [- punctuation-span "Forall" pi (posinfo-plus pi 1) -]
  [- var-span ff (Γ , pi' - x :` tk~) pi' x checking tk~ nothing -]
  [- TpQuant-span Γ e pi pi' x tk~ T (maybe-to-checking kₑ?)
       (kind-data Γ KdStar :: expected-kind-if Γ kₑ?)
       (check-for-kind-mismatch-if Γ "computed" kₑ? KdStar) -]
  return-when (TpAbs e x tk~ T~) KdStar

-- ι x : T₁. T₂
check-type Γ (ExTpIota pi pi' x T₁ T₂) kₑ? =
  Γ ⊢ T₁ ⇐ KdStar ↝ T₁~ /
  (Γ , pi' - x :` Tkt T₁~) ⊢ T₂ ⇐ KdStar ↝ T₂~ /
  let T₂~ = rename-var Γ (pi' % x) x T₂~ in
  [- punctuation-span "Iota" pi (posinfo-plus pi 1) -]
  [- Var-span (Γ , pi' - x :` Tkt T₁~) pi' x checking [ type-data Γ T₁~ ] nothing -]
  [- Iota-span Γ pi pi' x T₁~ T₂ (maybe-to-checking kₑ?)
       (kind-data Γ KdStar :: expected-kind-if Γ kₑ?)
       (check-for-kind-mismatch-if Γ "computed" kₑ? KdStar) -]
  return-when (TpIota x T₁~ T₂~) KdStar

-- {^ T ^} (generated by theta)
check-type Γ (ExTpNoSpans T pi) kₑ? = check-type Γ T kₑ? >>=spand return

-- [d] - T
check-type Γ (ExTpLet pi d T) kₑ? =
  check-let Γ d ff (type-start-pos T) (type-end-pos T) >>= λ where
    (Γ' , x , tv , σ , f) →
      case-ret-body {m = kₑ?} (check-type Γ' T kₑ?) λ T~ k~ →
      [- punctuation-span "Parens (let)" pi (type-end-pos T) -]
      [- TpLet-span pi (type-end-pos T) (maybe-to-checking kₑ?)
           (maybe-else' kₑ? (kind-data Γ k~) (expected-kind Γ) :: [ tv ]) -]
      return-when (σ T~) (σ k~)

-- T · T'
check-type Γ (ExTpApp T T') kₑ? =
  Γ ⊢ T ↝ T~ ⇒ kₕ /
  Γ ⊢ kₕ =β= λ where
    (KdAbs x (Tkk dom) cod) →
      Γ ⊢ T' ⇐ dom ↝ T'~ /
      let cod' = [ Γ - T'~ / x ] cod in
      [- TpApp-span (type-start-pos T) (type-end-pos T') (maybe-to-checking kₑ?)
           (kind-data Γ cod' :: expected-kind-if Γ kₑ?)
           (check-for-kind-mismatch-if Γ "synthesized" kₑ? cod') -]
      return-when (TpAppTp T~ T'~) cod'
    kₕ' →
      untyped-type Γ T' >>= T'~ /
      [- TpApp-span (type-start-pos T) (type-end-pos T') (maybe-to-checking kₑ?)
           (head-kind Γ kₕ' :: expected-kind-if Γ kₑ?)
           (unless (is-hole kₕ') $
              "The synthesized kind of the head does not allow it to be applied" ^
              " to a type argument") -]
      return-when (TpAppTp T~ T'~) (KdHole (type-start-pos T))

-- T t
check-type Γ (ExTpAppt T t) kₑ? =
  Γ ⊢ T ↝ T~ ⇒ kₕ /
  Γ ⊢ kₕ =β= λ where
    (KdAbs x (Tkt dom) cod) →
      Γ ⊢ t ⇐ dom ↝ t~ /
      let cod' = [ Γ - t~ / x ] cod in
      [- TpAppt-span (type-start-pos T) (term-end-pos t) (maybe-to-checking kₑ?)
           (kind-data Γ cod' :: expected-kind-if Γ kₑ?)
           (check-for-kind-mismatch-if Γ "synthesized" kₑ? cod') -]
      return-when (TpAppTm T~ t~) cod'
    kₕ' →
      untyped-term Γ t >>= t~ /
      [- TpAppt-span (type-start-pos T) (term-end-pos t) (maybe-to-checking kₑ?)
           (head-kind Γ kₕ' :: expected-kind-if Γ kₑ?)
           (unless (is-hole kₕ') $
              "The synthesized kind of the head does not allow it to be applied" ^
              " to a term argument") -]
      return-when (TpAppTm T~ t~) (KdHole (type-start-pos T))

-- T ➔/➾ T'
check-type Γ (ExTpArrow T e T') kₑ? =
  Γ ⊢ T ⇐ KdStar ↝ T~ /
  Γ ⊢ T' ⇐ KdStar ↝ T'~ /
  [- TpArrow-span T T' (maybe-to-checking kₑ?)
       (kind-data Γ KdStar :: expected-kind-if Γ kₑ?)
       (check-for-kind-mismatch-if Γ "computed" kₑ? KdStar) -]
  return-when (TpAbs e ignored-var (Tkt T~) T'~) KdStar

-- { t₁ ≃ t₂ }
check-type Γ (ExTpEq pi t₁ t₂ pi') kₑ? =
  untyped-term Γ t₁ >>= t₁~ /
  untyped-term Γ t₂ >>= t₂~ /
  [- punctuation-span "Parens (equation)" pi pi' -]
  [- TpEq-span pi pi' (maybe-to-checking kₑ?)
       (kind-data Γ KdStar :: expected-kind-if Γ kₑ?)
       (check-for-kind-mismatch-if Γ "computed" kₑ? KdStar) -]
  return-when (TpEq t₁~ t₂~) KdStar

-- ●
check-type Γ (ExTpHole pi) kₑ? =
  [- tp-hole-span Γ pi kₑ? (maybe-to-checking kₑ?) [] -]
  return-when (TpHole pi) (KdHole pi)

-- λ x : tk. T
check-type Γ (ExTpLam pi pi' x tk T) kₑ? =
  [- punctuation-span "Lambda (type)" pi (posinfo-plus pi 1) -]
  Γ ⊢ tk ↝ tk~ /
  case-ret
    ((Γ , pi' - x :` tk~) ⊢ T ↝ T~ ⇒ k /
     let kₛ = KdAbs x tk~ (rename-var Γ (pi' % x) x k) in
     [- var-span ff (Γ , pi' - x :` tk~) pi' x checking tk~ nothing -]
     [- TpLambda-span Γ pi pi' x tk~ T synthesizing [ kind-data Γ kₛ ] nothing -]
     return2 (TpLam x tk~ (rename-var Γ (pi' % x) x T~)) kₛ)
    λ kₑ →
      (Γ ⊢ kₑ =β= λ where
        (KdAbs x' tk' k) →
          (Γ , pi' - x :` tk~) ⊢ T ⇐ (rename-var Γ x' (pi' % x) k) ↝ T~ /
          let xₙ = if x =string ignored-var && is-free-in x' k then x' else x in
          return (xₙ , rename-var Γ (pi' % x) xₙ T~ , lambda-bound-conv? Γ x tk' tk~ [])
        kₕ →
          (Γ , pi' - x :` tk~) ⊢ T ↝ T~ ⇒ _ /
          return (x , rename-var Γ (pi' % x) x T~ , [] , unless (is-hole kₕ)
              "The expected kind is not an arrow- or Pi-kind")
      ) >>= λ where
        (xₙ , T~ , tvs , e?) →
          [- var-span ff (Γ , pi' - x :` tk~) pi' x checking tk~ nothing -]
          [- TpLambda-span Γ pi pi' x tk~ T checking (expected-kind Γ kₑ :: tvs) e? -]
          return (TpLam xₙ tk~ T~)

-- (T)
check-type Γ (ExTpParens pi T pi') kₑ? =
  [- punctuation-span "Parens (type)" pi pi' -]
  check-type Γ T kₑ?

-- x
check-type Γ (ExTpVar pi x) kₑ? =
  maybe-else' (ctxt-lookup-type-var Γ x)
    ([- TpVar-span Γ pi x (maybe-to-checking kₑ?) (expected-kind-if Γ kₑ?)
          (just "Undefined type variable") -]
     return-when (TpVar x) (KdHole pi)) λ where
    (qx , as , k) →
      [- TpVar-span Γ pi x (maybe-to-checking kₑ?)
           (expected-kind-if Γ kₑ? ++ [ kind-data Γ k ])
           (check-for-kind-mismatch-if Γ "computed" kₑ? k) -]
      return-when (apps-type (TpVar qx) as) k
  


-- Π x : tk. k
check-kind Γ (ExKdAbs pi pi' x tk k) =
  Γ ⊢ tk ↝ tk~ /
  Γ , pi' - x :` tk~ ⊢ k ↝ k~ /
  [- KdAbs-span Γ pi pi' x tk~ k checking nothing -]
  [- var-span ff Γ pi' x checking tk~ nothing -]
  [- punctuation-span "Pi (kind)" pi (posinfo-plus pi 1) -]
  return (KdAbs x tk~ (rename-var Γ (pi' % x) x k~))

-- tk ➔ k
check-kind Γ (ExKdArrow tk k) =
  Γ ⊢ tk ↝ tk~ /
  Γ ⊢ k ↝ k~ /
  [- KdArrow-span tk k checking nothing -]
  return (KdAbs ignored-var tk~ k~)

-- ●
check-kind Γ (ExKdHole pi) =
  [- kd-hole-span pi checking -]
  return (KdHole pi)

-- (k)
check-kind Γ (ExKdParens pi k pi') =
  [- punctuation-span "Parens (kind)" pi pi' -]
  check-kind Γ k

-- ★
check-kind Γ (ExKdStar pi) =
  [- Star-span pi checking nothing -]
  return KdStar

-- κ as...
check-kind Γ (ExKdVar pi κ as) =
  case ctxt-lookup-kind-var-def Γ κ of λ where
    nothing →
      [- KdVar-span Γ (pi , κ) (args-end-pos (posinfo-plus-str pi κ) as)
           [] checking [] (just "Undefined kind variable") -]
      return (KdHole pi)
    (just (ps , k)) →
      check-args Γ as ps >>= λ as~ →
      [- KdVar-span Γ (pi , κ) (args-end-pos (posinfo-plus-str pi κ) as)
          ps checking (params-data Γ ps)
          (when (length as < length ps)
            ("Needed " ^ ℕ-to-string (length ps ∸ length as)
              ^ " further argument(s)")) -]
      return (fst (subst-params-args' Γ ps as~ k))


check-tpkd Γ (ExTkt T) = Tkt <$> check-type Γ T (just KdStar)
check-tpkd Γ (ExTkk k) = Tkk <$> check-kind Γ k

check-args Γ (ExTmArg me t :: as) (Param me' x (Tkt T) :: ps) =
  Γ ⊢ t ⇐ T ↝ t~ /
  let e-s = mk-span "Argument" (term-start-pos t) (term-end-pos t)
              [ expected-type Γ T ] (just "Mismatched argument erasure") 
      e-m = λ r → if me iff me' then return {F = spanM} r else ([- e-s -] return {F = spanM} r) in
  check-args Γ as (subst-params Γ t~ x ps) >>= λ as~ →
  e-m ((if me then inj₂ (inj₁ t~) else inj₁ t~) :: as~)
check-args Γ (ExTpArg T :: as) (Param _ x (Tkk k) :: ps) =
  Γ ⊢ T ⇐ k ↝ T~ /
  check-args Γ as (subst-params Γ T~ x ps) >>= λ as~ →
  return (inj₂ (inj₂ T~) :: as~)
check-args Γ (ExTmArg me t :: as) (Param _ x (Tkk k) :: ps) =
  [- mk-span "Argument" (term-start-pos t) (term-end-pos t) [ expected-kind Γ k ]
       (just "Expected a type argument") -]
  return []
check-args Γ (ExTpArg T :: as) (Param me x (Tkt T') :: ps) =
  [- mk-span "Argument" (type-start-pos T) (type-end-pos T) [ expected-type Γ T' ]
       (just ("Expected a" ^ (if me then "n erased" else "") ^ " term argument")) -]
  return []
check-args Γ (a :: as) [] =
  let range = case a of λ {(ExTmArg me t) → term-start-pos t , term-end-pos t;
                           (ExTpArg T) → type-start-pos T , type-end-pos T} in
  check-args Γ as [] >>= λ as~ →
  [- mk-span "Argument" (fst range) (snd range) [] (just "Too many arguments given") -]
  return []
check-args Γ [] _ = return []

check-erased-margs : ctxt → posinfo → posinfo → term → maybe type → spanM ⊤
check-erased-margs Γ pi pi' t T? =
  let psₑ = foldr (λ {(Param me x tk) psₑ → if me then x :: psₑ else psₑ}) [] (ctxt.ps Γ)
      fvs = free-vars (erase t)
      e = list-any (stringset-contains fvs) psₑ in
  if e then spanM-add (erased-marg-span Γ pi pi' T?) else spanMok

check-let Γ (ExDefTerm pi x (just Tₑ) t) e? fm to =
  Γ ⊢ Tₑ ⇐ KdStar ↝ Tₑ~ /
  Γ ⊢ t ⇐ Tₑ~ ↝ t~ /
  elim-pair (compileFail-in Γ t~) λ tvs e →
  [- Var-span (Γ , pi - x :` Tkt Tₑ~) pi x checking (type-data Γ Tₑ~ :: tvs) e -]
  return
    (ctxt-term-def pi localScope opacity-open x (just t~) Tₑ~ Γ ,
     pi % x ,
     binder-data Γ pi x (Tkt Tₑ~) e? (just t~) fm to ,
     (λ {ed} T' → [ Γ - t~ / (pi % x) ] T') ,
     (λ t' → LetTm (e? || ~ is-free-in (pi % x) (erase t')) x nothing t~
                   ([ Γ - Var x / (pi % x) ] t')))
check-let Γ (ExDefTerm pi x nothing t) e? fm to =
  Γ ⊢ t ↝ t~ ⇒ Tₛ~ /
  elim-pair (compileFail-in Γ t~) λ tvs e →
  let Γ' = ctxt-term-def pi localScope opacity-open x (just t~) Tₛ~ Γ in
   [- Var-span Γ' pi x synthesizing (type-data Γ Tₛ~ :: tvs) e -]
   return
     (Γ' ,
     pi % x ,
     binder-data Γ pi x (Tkt Tₛ~) e? (just t~) fm to ,
     (λ {ed} T' → [ Γ - t~ / (pi % x) ] T') ,
     (λ t' → LetTm (e? || ~ is-free-in (pi % x) (erase t')) x nothing t~
                   ([ Γ - Var x / (pi % x) ] t')))
check-let Γ (ExDefType pi x k T) e? fm to =
  Γ ⊢ k ↝ k~ /
  Γ ⊢ T ⇐ k~ ↝ T~ /
  [- TpVar-span (Γ , pi - x :` Tkk k~) pi x checking [ kind-data Γ k~ ] nothing -]
  return
    (ctxt-type-def pi localScope opacity-open x (just T~) k~ Γ ,
     pi % x ,
     binder-data Γ pi x (Tkk k~) e? (just T~) fm to ,
     (λ {ed} T' → [ Γ - T~ / (pi % x) ] T') ,
     (λ t' → LetTp x k~ T~ ([ Γ - TpVar x / (pi % x) ] t')))

check-case Γ (ExCase pi x cas t) es Dₓ cs ρₒ as dps Tₘ cast-tm cast-tp =
  [- pattern-span pi x cas -]
  maybe-else'
    (trie-lookup (ctxt.qual Γ) x >>= uncurry λ x' _ →
     trie-lookup cs x' >>= λ T →
     just (x' , T))
    (let e = maybe-else' (trie-lookup es x)
               ("This is not a constructor of " ^
                  unqual-local (unqual-all (ctxt.qual Γ) Dₓ))
               λ _ → "This case is unreachable" in
     [- pattern-ctr-span Γ pi x [] [] (just e) -]
     return2 (Case x [] (Hole pi) []) cs)
    λ where
     (x' , Tₕ , ps , is) →
      decl-args Γ cas ps empty-trie ρₒ [] (const spanMok) >>= λ where
        (Γ' , cas' , e , σ , ρ , tvs , sm) →
          let rs = tmtps-to-args' Γ' σ (drop dps is)
              Tₘ' = TpAppTm (apps-type Tₘ rs)
                            (app-caseArgs (cast-tm Γ') (cast-tp Γ') (recompose-apps as (Var x')) (zip cas cas'))
              Tₘ' = hnf Γ' unfold-no-defs Tₘ' in
          Γ' ⊢ t ⇐ Tₘ' ↝ t~ /
          sm t~ >>
          [- pattern-clause-span pi t (reverse tvs) -]
          [- pattern-ctr-span Γ' pi x cas' [] e -]
          return2 (Case x'
                     (subst-case-args cas' Γ ρₒ)
                     (subst-renamectxt Γ ρ t~)
                     (args-to-tmtps (as ++ (subst-renamectxt Γ ρ -arg_ <$> rs))))
                  (trie-remove cs x')
  where
  subst-case-args : case-args → ctxt → renamectxt → case-args
  subst-case-args [] Γ ρ = []
  subst-case-args (CaseArg e x tk? :: cs) Γ ρ =
    CaseArg e x (subst-renamectxt Γ ρ -tk_ <$> tk?) ::
      subst-case-args cs (ctxt-var-decl x Γ) (renamectxt-insert ρ x x)

  free-in-term : var → term → err-m
  free-in-term x t = when (is-free-in x (erase t))
                       "Erased argument occurs free in the body of the term"
  tmtp-to-arg' : ctxt → trie (Σi exprd ⟦_⟧) → tmtp → arg
  tmtp-to-arg' = λ Γ σ → either-else (Arg ∘ substs Γ σ) (ArgTp ∘ substs Γ σ)
  tmtps-to-args' : ctxt → trie (Σi exprd ⟦_⟧) → 𝕃 tmtp → args
  tmtps-to-args' = λ Γ σ → tmtp-to-arg' Γ σ <$>_
  app-caseArgs : (term → type → term) → (type → kind → type) → term → 𝕃 (ex-case-arg × case-arg) → term
  app-caseArgs tf Tf = foldl λ where
    (ExCaseArg _ pi x , CaseArg me _ tk?) t → elim-pair (me , tk?) λ where
      tt (just (Tkt T)) → AppEr t (tf (Var (pi % x)) T)
      tt (just (Tkk k)) → AppTp t (Tf (TpVar (pi % x)) k)
      ff (just (Tkt T)) → App t (tf (Var (pi % x)) T)
      _ _ → t
  spos = term-start-pos t
  epos = term-end-pos t
  add-case-arg : ∀ {X Y} → ctxt → var → var → case-arg → spanM (X × case-args × Y) → spanM (X × case-args × Y)
  add-case-arg Γ x xₙ ca m = m >>=c λ X → return2 X ∘ map-fst λ cas → ca :: subst-case-args cas Γ (renamectxt-single x xₙ)
  decl-args : ctxt → ex-case-args → params → trie (Σi exprd ⟦_⟧) →
                renamectxt → 𝕃 tagged-val → (term → spanM ⊤) →
              spanM (ctxt × case-args × err-m × trie (Σi exprd ⟦_⟧) ×
                     renamectxt × 𝕃 tagged-val × (term → spanM ⊤))
  decl-args Γ (ExCaseArg ExCaseArgTp pi x :: as) (Param me x' (Tkt T) :: ps) σ ρ xs sm =
    let T' = substs Γ σ T
        Γ' = ctxt-var-decl-loc pi x Γ
        xₙ = if x =string ignored-var then x' else x in
    add-case-arg Γ' (pi % x) xₙ (CaseArg tt xₙ (just (Tkt T'))) $
    decl-args Γ' as ps
      (trie-insert σ x' (, TpVar (pi % x)))
      (renamectxt-insert ρ (pi % x) xₙ)
      (binder-data Γ' pi x (Tkt T') Erased nothing spos epos :: xs)
      λ t → [- TpVar-span Γ' pi x checking [ expected-type Γ T' ]
                 (just ("This type argument should be a" ^
                     (if me then "n erased term" else " term"))) -] sm t
  decl-args Γ (ExCaseArg ExCaseArgTp pi x :: as) (Param _ x' (Tkk k) :: ps) σ ρ xs sm =
    let k' = substs Γ σ k
        Γ' = ctxt-type-decl pi x k' Γ
        xₙ = if x =string ignored-var then x' else x in
    add-case-arg Γ' (pi % x) xₙ (CaseArg tt xₙ (just (Tkk k'))) $
    decl-args Γ' as ps
      (trie-insert σ x' (, TpVar (pi % x)))
      (renamectxt-insert ρ (pi % x) xₙ)
      (binder-data Γ' pi x (Tkk k') Erased nothing spos epos :: xs)
      λ t → [- TpVar-span Γ' pi x checking [ kind-data Γ k' ] (free-in-term x t) -] sm t
  decl-args Γ (ExCaseArg me pi x :: as) (Param me' x' (Tkt T) :: ps) σ ρ xs sm =
    let T' = substs Γ σ T
        e₁ = when (ex-case-arg-erased me xor me') "Mismatched erasure of term argument"
        e₂ = λ t → maybe-if (ex-case-arg-erased me) >> free-in-term x t
        Γ' = Γ , pi - x :` (Tkt T')
        xₙ = if x =string ignored-var then x' else x in
    (add-case-arg Γ' (pi % x) xₙ (CaseArg me' xₙ (just (Tkt T'))) $
    decl-args Γ' as ps
      (trie-insert σ x' (, Var (pi % x)))
      (renamectxt-insert ρ (pi % x) xₙ)
      (binder-data Γ' pi x (Tkt T') (ex-case-arg-erased me) nothing spos epos :: xs)
      λ t → [- Var-span Γ' pi x checking [ type-data Γ T' ] (e₁ ||-maybe e₂ t) -] sm t)
  decl-args Γ (ExCaseArg me pi x :: as) (Param me' x' (Tkk k) :: ps) σ ρ xs sm =
    let k' = substs Γ σ k
        Γ' = ctxt-var-decl-loc pi x Γ
        xₙ = if x =string ignored-var then x' else x in
    add-case-arg Γ' (pi % x) xₙ (CaseArg tt xₙ (just (Tkk k'))) $
    decl-args Γ' as ps
      (trie-insert σ x' (, Var (pi % x)))
      (renamectxt-insert ρ (pi % x) xₙ)
      (binder-data Γ' pi x (Tkk k') (ex-case-arg-erased me) nothing spos epos :: xs)
      λ t → [- Var-span Γ' pi x checking [ expected-kind Γ k' ]
                 (just "This term argument should be a type") -] sm t
  decl-args Γ [] [] σ ρ xs sm =
    return (Γ , [] , nothing , σ , ρ , xs , sm)
  decl-args Γ as [] σ ρ xs sm =
    return (Γ , [] , just (ℕ-to-string (length as) ^ " too many arguments supplied") ,
              σ , ρ , xs , sm)
  decl-args Γ [] ps σ ρ xs sm =
    return (Γ , params-to-case-args (substs-params Γ σ ps) ,
            just (ℕ-to-string (length ps) ^ " more arguments expected") , σ , ρ , xs , sm)

check-cases Γ ms Dₓ cs ρ as dps Tₘ cast-tm cast-tp =
  foldr {B = stringset → trie (type × params × 𝕃 tmtp) →
              spanM (cases × trie (type × params × 𝕃 tmtp))}
    (λ m x es cs' → 
      check-case Γ m es Dₓ cs' ρ as dps Tₘ cast-tm cast-tp >>=c λ m~ cs →
      x (stringset-insert es (ex-case-ctr m)) cs >>=c λ ms~ → 
      return2 (m~ :: ms~))
    (λ es → return2 [])
    ms
    empty-stringset
    (trie-map (decompose-ctr-type Γ) cs)
  >>=c λ ms~ missing-cases →
  let xs = map (map-snd snd) $ trie-mappings missing-cases
      csf = uncurry₂ λ Tₕ ps as →
              rope-to-string $ strRun Γ $
                strVar (unqual-all (ctxt.qual Γ) Tₕ) >>str args-to-string (params-to-args ps)
      e = "Missing patterns: " ^ 𝕃-to-string csf ", " xs in
  return2 ms~ (unless (iszero (length xs)) e)

check-refinement Γ Tₘ kₘ s =
  check-type (qualified-ctxt Γ) (resugar Tₘ) (just kₘ) empty-spans >>= uncurry λ Tₘ' s' →
    return $ (λ x → x , s) $
      Tₘ' ,
      [ to-string-tag "computed motive" Γ Tₘ ] ,
      (when (spans-have-error s') "We could not compute a well-kinded motive")

get-datatype-info-from-head-type Γ X as = return $ maybe-else' (data-lookup Γ X as)
    (inj₁ $ "The head type of the subterm is not a datatype" , [ head-type Γ (TpVar X) ])
    (λ μ → inj₂ μ)

check-sigma-evidence Γ tₑ? X as = maybe-else' tₑ?
  (get-datatype-info-from-head-type Γ X as >>=s λ d → return $ inj₂ (sigma-build-evidence X d , id , d))
  (λ tₑ →
    Γ ⊢ tₑ ↝ tₑ~ ⇒ T /
    let ev-err = inj₁ $
                   ("The synthesized type of the evidence does not prove " ^
                      unqual-local (unqual-all (ctxt.qual Γ) X) ^ " is a datatype") ,
                    [ to-string-tag "evidence type" Γ T ] in
    case decompose-tpapps (hnf Γ unfold-head-elab T) of λ where
      (TpVar X' , as') → case reverse as' of λ where
        (Ttp T :: as') → return $ if ~ conv-type Γ T (TpVar X)
          then ev-err
          else maybe-else
            ev-err
            (λ {d@(mk-data-info X Xₒ asₚ asᵢ mps kᵢ k cs csₚₛ eds gds) →
              inj₂ (tₑ~ , (App $ recompose-apps (asₚ ++ tmtps-to-args Erased asᵢ) $
                                   Var $ data-to/ X) , d)})
            -- AS: it looks like we are reversing as' twice, so not reversing at all? 
            (data-lookup-mu Γ X X' $ reverse as' ++ as)
            -- TODO: Make sure "X" isn't a _defined_ type, but a _declared_ one!
            --       This way we avoid the possibility that "as" has arguments
            --       to parameters in it, but only to indices.
            -- Also TODO: Make sure that parameters are equal in above conversion check!
        _ → return ev-err
      _ → return ev-err
  )

ctxt-mu-decls : ctxt → term → indices → type → datatype-info → posinfo → posinfo → posinfo → var → (cases → spanM ⊤) × ctxt × 𝕃 tagged-val × renamectxt × (ctxt → term → type → term) × (ctxt → type → kind → type)
ctxt-mu-decls Γ t is Tₘ (mk-data-info X Xₒ asₚ asᵢ ps kᵢ k cs csₚₛ eds gds) pi₁ pi₂ pi₃ x =
  let X' = mu-Type/ x
      xₘᵤ = mu-isType/ x
      qXₘᵤ = data-Is/ X
      qXₜₒ = data-to/ X
      qX' = pi₁ % X'
      qxₘᵤ = pi₁ % xₘᵤ
      qx = pi₁ % x
      Tₘᵤ = TpAppTp (flip apps-type asₚ $ TpVar qXₘᵤ) $ TpVar qX'
      Γ' = ctxt-term-def pi₁ localScope opacity-open xₘᵤ nothing Tₘᵤ $
           ctxt-datatype-decl X qx asₚ $
           ctxt-type-decl pi₁ X' k Γ
      freshₓ = fresh-var (add-indices-to-ctxt is Γ') (maybe-else "x" id (is-var (Ttm t)))
      Tₓ = hnf Γ' unfold-no-defs (indices-to-alls is $ TpAbs ff freshₓ (Tkt $ indices-to-tpapps is $ TpVar qX') $ TpAppTm (indices-to-tpapps is Tₘ) $ Phi (Beta (Var freshₓ) (Var freshₓ)) (App (indices-to-apps is $ AppEr (AppTp (flip apps-term asₚ $ Var qXₜₒ) $ TpVar qX') $ Var qxₘᵤ) $ Var freshₓ) (Var freshₓ))
      Γ'' = ctxt-term-decl pi₁ x Tₓ Γ'
      e₂? = unless (X =string Xₒ) "Abstract datatypes can only be pattern matched by σ"
      e₃ = λ x → just $ x ^ " occurs free in the erasure of the body (not allowed)"
      cs-fvs = stringset-contains ∘' free-vars-cases ∘' erase-cases
      e₃ₓ? = λ cs x → maybe-if (cs-fvs cs x) >> e₃ x
      e₃? = λ cs → e₃ₓ? cs (mu-isType/ x) ||-maybe e₃ₓ? cs (mu-Type/ x) in
    (λ cs → [- var-span NotErased Γ'' pi₁ x checking (Tkt Tₓ) (e₂? ||-maybe e₃? cs) -] spanMok) ,
     Γ'' ,
    (binder-data Γ'' pi₁ X' (Tkk k) Erased nothing pi₂ pi₃ ::
     binder-data Γ'' pi₁ xₘᵤ (Tkt Tₘᵤ) Erased nothing pi₂ pi₃ ::
     binder-data Γ'' pi₁ x (Tkt Tₓ) NotErased nothing pi₂ pi₃ ::
     to-string-tag X' Γ'' k ::
     to-string-tag xₘᵤ Γ'' Tₘᵤ ::
     to-string-tag x Γ'' Tₓ :: []) ,
    renamectxt-insert* empty-renamectxt
      ((qX' , X') :: (qxₘᵤ , xₘᵤ) :: (qx , x) :: []) ,
    let cg = qX' , recompose-tpapps (args-to-tmtps asₚ) (TpVar qx) , AppEr (AppTp (recompose-apps asₚ (Var qXₜₒ)) (TpVar qX')) (Var qxₘᵤ) in
    flip (mk-ctr-fmap-η? ff ∘ ctxt-datatype-undef qX') cg ,
    flip (mk-ctr-fmapₖ-η? ff ∘ ctxt-datatype-undef qX') cg

check-mu Γ pi pi' x t Tₘ? pi'' cs pi''' Tₑ? =
  check-term Γ t nothing >>=c λ t~ T →
  let no-motive-err = just "A motive is required when synthesizing"
      no-motive = return (nothing , [] , no-motive-err) in
  case decompose-tpapps (hnf Γ unfold-head-elab T) of λ where
    (TpVar X , as) →
      get-datatype-info-from-head-type Γ X as on-fail
       (uncurry λ e tvs → spanM-add (Mu-span Γ pi pi''' nothing (maybe-to-checking Tₑ?)
         (expected-type-if Γ Tₑ? ++ tvs) $ just e) >>
        return-when {m = Tₑ?} (Hole pi) (TpHole pi))
       >>=s λ where
        (d @ (mk-data-info Xₒ _ asₚ asᵢ ps kᵢ k cs' csₚₛ eds gds)) →
          let Rₓ = mu-Type/ x; qRₓ = pi' % Rₓ
              Γₘ = data-highlight (ctxt-type-decl pi' Rₓ k Γ) qRₓ
              ρₘ = subst Γₘ (recompose-tpapps (args-to-tmtps asₚ) (TpVar Xₒ)) qRₓ
              ρₘ' = subst Γₘ (TpVar Rₓ) qRₓ
              eₘ = λ Tₘ → when (positivity.negₒ qRₓ (positivity.type+ qRₓ Γₘ (hnf-ctr Γₘ qRₓ Tₘ)))
                            (Rₓ ^ " occurs negatively in the motive")
          in
              maybe-map (λ Tₘ → check-type Γₘ Tₘ (just kᵢ)) Tₘ? >>=? λ Tₘ?' →
              let is = kind-to-indices Γ kᵢ
                  eₘ = Tₘ?' >>= eₘ
                  ret-tp = λ ps as t → maybe-else' Tₘ?' Tₑ? (λ Tₘ → just $ hnf Γ unfold-head-elab (TpAppTm (apps-type (ρₘ Tₘ) $
                              tmtps-to-args NotErased (drop (length ps) as)) t)) in
              (maybe-else' Tₘ?'
                 (return Tₑ? on-fail no-motive >>=m λ Tₑ →
                  let Tₘ = refine-motive Γ is (asᵢ ++ [ Ttm t~ ]) Tₑ in
                  check-refinement Γ Tₘ kᵢ >>=c λ Tₘ → return2 (just Tₘ))
                 λ Tₘ → return (just Tₘ , [] , nothing))
              >>=c λ Tₘ → uncurry λ tvs₁ e₁ →
              let Tₘ = maybe-else' Tₘ (TpHole pi) id
                  is = drop-last 1 is
                  reduce-cs = map λ {(Ctr x T) → Ctr x $ hnf Γ unfold-no-defs T}
                  fcs = λ y → inst-ctrs Γ ps asₚ (map-snd (rename-var {TYPE} Γ Xₒ y) <$> cs')
                  cs' = reduce-cs $ fcs (mu-Type/ (pi' % x)) in
              case
                (ctxt-mu-decls Γ t~ is Tₘ d pi' pi'' pi''' x) of λ where
                (sm , Γ' , bds , ρ , cast-tm , cast-tp) →
                  let cs'' = foldl (λ {(Ctr x T) σ → trie-insert σ x T}) empty-trie cs'
                      drop-ps = 0
                      scrutinee = t~
                      Tᵣ = ret-tp ps (args-to-tmtps asₚ ++ asᵢ) scrutinee in
                  check-cases Γ' cs Xₒ cs'' ρ asₚ drop-ps Tₘ cast-tm cast-tp >>=c λ cs~ e₂ →
                  let e₃ = maybe-else' Tᵣ
                             (just "A motive is required when synthesizing")
                             (check-for-type-mismatch-if Γ "synthesized" Tₑ?) in
                  [- Mu-span Γ pi pi''' Tₘ?' (maybe-to-checking Tₑ?)
                         (expected-type-if Γ Tₑ? ++
                           maybe-else' Tᵣ [] (λ Tᵣ → [ type-data Γ Tᵣ ]) ++
                           tvs₁ ++
                           bds)
                         (e₁ ||-maybe (e₂ ||-maybe (e₃ ||-maybe eₘ))) -]
                  sm cs~ >>
                  return-when {m = Tₑ?}
                    (subst-renamectxt Γ ρ (Mu x t~ (just (ρₘ' Tₘ)) d cs~))
                    (maybe-else' Tᵣ (TpHole pi) id)
    (Tₕ , as) →
      [- Mu-span Γ pi pi''' nothing (maybe-to-checking Tₑ?)
        [ head-type Γ Tₕ ] (just "The head type of the subterm is not a datatype") -]
      return-when {m = Tₑ?} (Hole pi) (TpHole pi)

check-sigma Γ pi t? t Tₘ? pi'' cs pi''' Tₑ? = 
  check-term Γ t nothing >>=c λ t~ T →
  let no-motive-err = just "A motive is required when synthesizing"
      no-motive = return (nothing , [] , no-motive-err) in
  case decompose-tpapps (hnf Γ unfold-head-elab T) of λ where
    (TpVar X , as) →
      check-sigma-evidence Γ t? X as on-fail
       (uncurry λ e tvs → spanM-add (Sigma-span Γ pi pi''' nothing (maybe-to-checking Tₑ?)
         (expected-type-if Γ Tₑ? ++ tvs) $ just e) >>
        return-when {m = Tₑ?} (Hole pi) (TpHole pi))
       >>=s λ where
        (tₑ~ , cast , d @ (mk-data-info Xₒ _ asₚ asᵢ ps kᵢ k cs' csₚₛ eds gds)) →
              maybe-map (λ Tₘ → check-type Γ Tₘ (just kᵢ)) Tₘ? >>=? λ Tₘ?' →
              let is = kind-to-indices Γ kᵢ
                  ret-tp = λ ps as t → maybe-else' Tₘ?' Tₑ? (λ Tₘ → just $ hnf Γ unfold-head-elab (TpAppTm (apps-type Tₘ $
                              tmtps-to-args NotErased (drop (length ps) as)) t)) in
              (maybe-else' Tₘ?'
                 (return Tₑ? on-fail no-motive >>=m λ Tₑ →
                  let Tₘ = refine-motive Γ is (asᵢ ++ [ Ttm t~ ]) Tₑ in
                  check-refinement Γ Tₘ kᵢ >>=c λ Tₘ → return2 (just Tₘ))
                 λ Tₘ → return (just Tₘ , [] , nothing))
              >>=c λ Tₘ → uncurry λ tvs₁ e₁ →
              let Tₘ = maybe-else' Tₘ (TpHole pi) id
                  reduce-cs = map λ {(Ctr x T) → Ctr x $ hnf Γ unfold-no-defs T}
                  fcs = λ y → inst-ctrs Γ ps asₚ (map-snd (rename-var {TYPE} Γ Xₒ y) <$> cs')
                  cs' = reduce-cs $ if Xₒ =string X then csₚₛ else fcs X in
              let sm = const spanMok
                  ρ = empty-renamectxt
                  cast-tm = (λ Γ t T → t)
                  cast-tp = (λ Γ T k → T) 
                  cs'' = foldl (λ {(Ctr x T) σ → trie-insert σ x T}) empty-trie cs'
                  drop-ps = maybe-else 0 length (when (Xₒ =string X) ps)
                  scrutinee = cast t~
                  Tᵣ = ret-tp ps (args-to-tmtps asₚ ++ asᵢ) scrutinee in
                 check-cases Γ cs Xₒ cs'' ρ asₚ drop-ps Tₘ cast-tm cast-tp >>=c λ cs~ e₂ →
                 let e₃ = maybe-else' Tᵣ
                             (just "A motive is required when synthesizing")
                             (check-for-type-mismatch-if Γ "synthesized" Tₑ?) in
                  [- Sigma-span Γ pi pi''' Tₘ?' (maybe-to-checking Tₑ?)
                         (expected-type-if Γ Tₑ? ++
                           maybe-else' Tᵣ [] (λ Tᵣ → [ type-data Γ Tᵣ ]) ++
                           tvs₁)
                         (e₁ ||-maybe (e₂ ||-maybe e₃)) -]
                  sm cs~ >>
                  return-when {m = Tₑ?}
                    (subst-renamectxt Γ ρ (Sigma (just tₑ~) t~ (just Tₘ) d cs~))
                    (maybe-else' Tᵣ (TpHole pi) id)
    (Tₕ , as) →
      [- Sigma-span Γ pi pi''' nothing (maybe-to-checking Tₑ?)
        [ head-type Γ Tₕ ] (just "The head type of the subterm is not a datatype") -]
      return-when {m = Tₑ?} (Hole pi) (TpHole pi)


