import cedille-options
open import general-util
module classify (options : cedille-options.options) {mF : Set → Set} {{_ : monad mF}} where

open import lib

open import cedille-types
open import constants
open import conversion
open import ctxt
open import datatype-functions
open import free-vars
open import rename
open import rewriting
open import meta-vars options {mF}
open import spans options {mF}
open import subst
open import syntax-util
open import type-util
open import to-string options
--open import untyped-spans options {mF}

spanMr2 : ∀ {X Y} → X → Y → spanM (X × Y)
spanMr2 = curry spanMr

check-ret : ∀ {Y : Set} → maybe Y → Set → Set
check-ret {Y} T t = if isJust T then t else (t × Y)

return-when : ∀ {X Y} {m : maybe Y} → X → Y → spanM (check-ret m X)
return-when {X} {Y} {nothing} x u = spanMr2 x u
return-when {X} {Y} {just _} x u = spanMr x

case-ret : ∀ {X Y} {m : maybe Y} → spanM (X × Y) → (Y → spanM X) → spanM (check-ret m X)
case-ret {X} {Y} {nothing} n j = n
case-ret {X} {Y} {just y} n j = j y

case-ret-body : ∀ {X Y} {m : maybe Y} → spanM (check-ret m X) → (X → Y → spanM (check-ret m X)) → spanM (check-ret m X)
case-ret-body {X} {Y} {nothing} m f = m ≫=span uncurry f
case-ret-body {X} {Y} {just y} m f = m ≫=span λ x → f x y

{-# TERMINATING #-}
check-term : ctxt → ex-tm → (T? : maybe type) → spanM (check-ret T? term)
check-type : ctxt → ex-tp → (k? : maybe kind) → spanM (check-ret k? type)
check-kind : ctxt → ex-kd → spanM kind
check-tpkd : ctxt → ex-tk → spanM tpkd
check-args : ctxt → ex-args → params → spanM args
check-let : ctxt → ex-def → erased? → posinfo → posinfo → spanM (ctxt × var × tagged-val × (∀ {ed : exprd} → ⟦ ed ⟧ → ⟦ ed ⟧) × (term → term))

synth-tmtp' : ∀ {b X} → ctxt → if b then ex-tm else ex-tp → (if b then term else type → if b then type else kind → spanM X) → spanM X
synth-tmtp' {tt} Γ t f = check-term Γ t nothing ≫=span uncurry f
synth-tmtp' {ff} Γ T f = check-type Γ T nothing ≫=span uncurry f

check-tmtp' : ∀ {b X} → ctxt → if b then ex-tm else ex-tp → if b then type else kind → (if b then term else type → spanM X) → spanM X
check-tmtp' {tt} Γ t T f = check-term Γ t (just T) ≫=span f
check-tmtp' {ff} Γ T k f = check-type Γ T (just k) ≫=span f

check-tpkd' : ∀ {b X} → ctxt → if b then ex-kd else ex-tk → (if b then kind else tpkd → spanM X) → spanM X
check-tpkd' {tt} Γ k f = check-kind Γ k ≫=span f
check-tpkd' {ff} Γ k f = check-tpkd Γ k ≫=span f

untyped-term : ctxt → ex-tm → spanM term
untyped-type : ctxt → ex-tp → spanM type
untyped-kind : ctxt → ex-kd → spanM kind
untyped-tpkd : ctxt → ex-tk → spanM tpkd

lambda-bound-conv? : ctxt → var → tpkd → tpkd → 𝕃 tagged-val → 𝕃 tagged-val × err-m
lambda-bound-conv? Γ x tk tk' ts with conv-tpkd Γ tk tk'
...| tt = ts , nothing
...| ff = (to-string-tag-tk "declared classifier" Γ tk' :: to-string-tag-tk "expected classifier" Γ tk :: ts) , just "The classifier given for a λ-bound variable is not the one we expected"

id' = id

hnf-of : ∀ {X : Set} {ed} → ctxt → ⟦ ed ⟧ → (⟦ ed ⟧ → X) → X
hnf-of Γ t f = f (hnf Γ unfold-head-elab t)

[-_-]_ : ∀ {X} → span → spanM X → spanM X
[- s -] m = spanM-add s ≫span m


-- "⊢" = "\vdash" or "\|-"
-- "⇒" = "\r="
-- "⇐" = "\l="
infixr 2 hnf-of [-_-]_ id' check-tpkd' check-tmtp' synth-tmtp'
syntax synth-tmtp' Γ t (λ t~ → f) = Γ ⊢ t ↝ t~ ⇒ f
syntax check-tmtp' Γ t T f = Γ ⊢ t ⇐ T ↝ f
syntax check-tpkd' Γ k f = Γ ⊢ k ↝ f
syntax id' (λ x → f) = x / f -- Supposed to look like a horizontal bar (as in typing rules)
syntax hnf-of Γ t f = Γ ⊢ t =β= f

infix 4 _,_-_:`_
_,_-_:`_ : ctxt → posinfo → var → tpkd → ctxt
Γ , pi - x :` tk = ctxt-tk-decl pi x tk Γ


-- t [-]t'
check-term Γ (ExApp t e t') Tₑ? =
  {!!}

-- t ·T
check-term Γ (ExAppTp t T) Tₑ? =
  {!!}

-- β[<t?>][{t?'}]
check-term Γ (ExBeta pi t? t?') Tₑ? =
  {!!}

-- χ [T?] - t
check-term Γ (ExChi pi T? t) Tₑ? =
  (maybe-else' T?
    (check-term Γ t nothing)
    λ T → Γ ⊢ T ⇐ KdStar ↝ T~ /
          Γ ⊢ t ⇐ T~ ↝ t~ /
          spanMr (t~ , T~)
  ) ≫=span uncurry λ t~ T~ →
  [- Chi-span Γ pi (just T~) t (maybe-to-checking Tₑ?)
       (type-data Γ T~ :: expected-type-if Γ Tₑ?)
       (check-for-type-mismatch-if Γ
         (maybe-else' T? "synthesized" (const "computed")) Tₑ? T~) -]
  return-when t~ T~

-- δ [T?] - t
check-term Γ (ExDelta pi T? t) Tₑ? =
  {!!}

-- εlr[-?] t
check-term Γ (ExEpsilon pi lr -? t) Tₑ? =
  {!!}

-- ●
check-term Γ (ExHole pi) Tₑ? =
  [- hole-span Γ pi Tₑ? [] -]
  return-when (Hole pi) (TpHole pi)

-- [ t₁ , t₂ [@ Tₘ,?] ]
check-term Γ (ExIotaPair pi t₁ t₂ Tₘ? pi') Tₑ? =
  case-ret
    (maybe-else' Tₘ?
       ([- IotaPair-span pi pi' synthesizing []
             (just "Iota pairs require a specified type when synthesizing") -]
        return-when (Hole pi) (TpHole pi))
       λ {(ExGuide pi'' x T) → {!!}})
    λ Tₑ →
      {!!}

-- t.n
check-term Γ (ExIotaProj t n pi) Tₑ? =
  Γ ⊢ t ↝ t~ ⇒ T~ /
  let n? = case n of λ {"1" → just ι1; "2" → just ι2; _ → nothing} in
  maybe-else' n?
    ([- IotaProj-span t pi (maybe-to-checking Tₑ?) (expected-type-if Γ Tₑ?)
          (just "Iota-projections must use .1 or .2 only") -]
     return-when (Hole pi) (TpHole pi)) λ n →
    Γ ⊢ T~ =β= λ where
      (TpIota x T₁ T₂) →
        let Tᵣ = if n iff ι1 then T₁ else ([ Γ - t~ / x ] T₂) in
        [- IotaProj-span t pi (maybe-to-checking Tₑ?)
             (type-data Γ Tᵣ :: expected-type-if Γ Tₑ?)
             (check-for-type-mismatch-if Γ "synthesized" Tₑ? Tᵣ) -]
        return-when (IotaProj t~ n) Tᵣ
      (TpHole pi') →
        [- IotaProj-span t pi (maybe-to-checking Tₑ?) (expected-type-if Γ Tₑ?) nothing -]
        return-when (IotaProj t~ n) (TpHole pi')
      Tₕ~ →
        [- IotaProj-span t pi (maybe-to-checking Tₑ?)
             (head-type Γ Tₕ~ :: expected-type-if Γ Tₑ?) nothing -]
        return-when (IotaProj t~ n) (TpHole pi)

-- λ/Λ x [: T?]. t
check-term Γ (ExLam pi e pi' x T? t) Tₑ? =
  {!!}

-- [d] - t
check-term Γ (ExLet pi e? d t) Tₑ? =
  check-let Γ d e? (term-start-pos t) (term-end-pos t) ≫=span λ where
    (Γ' , x , tv , σ , f) →
      case-ret-body {m = Tₑ?} (check-term Γ' t Tₑ?) λ t~ T~ →
      [- punctuation-span "Parens (let)" pi (term-end-pos t) -]
      [- Let-span e? pi (term-end-pos t) (maybe-to-checking Tₑ?)
           (maybe-else' Tₑ? (type-data Γ T~) (expected-type Γ) :: [ tv ])
           (maybe-if (e? && is-free-in x t~) ≫maybe
            just (unqual-local x ^ "occurs free in the body of the term")) -]
      return-when (f t~) (σ T~)


-- open/close x - t
check-term Γ (ExOpen pi o pi' x t) Tₑ? =
  let Γ? = ctxt-clarify-def Γ o x
      e? = maybe-not Γ? ≫maybe just (x ^ " does not have a definition that can be " ^
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
  untyped-term Γ t₂ ≫=span λ t₂~ →
  Γ ⊢ t₌ ⇐ TpEq t₁~ t₂~ ↝ t₌~ /
  [- Phi-span pi pi' (maybe-to-checking Tₑ?)
       [ maybe-else' Tₑ? (type-data Γ T~) (expected-type Γ)] nothing -]
  return-when (Phi t₌~ t₁~ t₂~) T~

-- ρ[+]<ns> t₌ [@ Tₘ?] - t
check-term Γ (ExRho pi ρ+ <ns> t₌ Tₘ? t) Tₑ? =
  {!!}

-- ς t
check-term Γ (ExSigma pi t) Tₑ? =
  case-ret
    (Γ ⊢ t ↝ t~ ⇒ T /
     Γ ⊢ T =β= λ where
       (TpEq t₁ t₂) →
         spanMr2 (Sigma t~) (TpEq t₂ t₁)
       (TpHole _) →
         spanMr2 (Sigma t~) (TpHole pi)
       Tₕ →
         [- Sigma-span pi t synthesizing [ type-data Γ Tₕ ]
           (just "The synthesized type of the body is not an equation") -]
         spanMr2 (Sigma t~) (TpHole pi))
  λ Tₑ →
    Γ ⊢ Tₑ =β= λ where
      (TpEq t₁ t₂) →
        Γ ⊢ t ⇐ TpEq t₂ t₁ ↝ t~ /
          [- Sigma-span pi t checking [ expected-type Γ (TpEq t₁ t₂) ] nothing -]
          spanMr (Sigma t~)
      (TpHole _) → spanMr (Hole pi)
      Tₕ → [- Sigma-span pi t checking [ expected-type Γ Tₕ ]
                (just "The expected type is not an equation") -]
           spanMr (Hole pi)

-- θ t ts
check-term Γ (ExTheta pi θ t ts) Tₑ? =
  {!!}

-- μ[' / rec.] t [@ Tₘ?] {ms...}
check-term Γ (ExMu pi μ t Tₘ? pi' ms pi'') Tₑ? =
  {!!}

-- x
check-term Γ (ExVar pi x) Tₑ? =
  maybe-else' (ctxt-lookup-term-var Γ x)
    ([- Var-span Γ pi x (maybe-to-checking Tₑ?)
          (expected-type-if Γ Tₑ?)
          (just "Missing a type for a term variable") -]
     return-when (Hole pi) (TpHole pi))
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
  [- TpQuant-span Γ e pi pi' x tk~ T (maybe-to-checking kₑ?)
       (kind-data Γ KdStar :: expected-kind-if Γ kₑ?)
       (check-for-kind-mismatch-if Γ "computed" kₑ? KdStar) -]
  return-when (TpAbs e x tk~ T~) KdStar

-- ι x : T₁. T₂
check-type Γ (ExTpIota pi pi' x T₁ T₂) kₑ? =
  Γ ⊢ T₁ ⇐ KdStar ↝ T₁~ /
  (Γ , pi' - x :` Tkt T₁~) ⊢ T₂ ⇐ KdStar ↝ T₂~ /
  let T₂~ = rename-var Γ (pi' % x) x T₂~ in
  [- punctuation-span "Forall" pi (posinfo-plus pi 1) -]
  [- Iota-span Γ pi pi' x T₂~ T₂ (maybe-to-checking kₑ?)
       (kind-data Γ KdStar :: expected-kind-if Γ kₑ?)
       (check-for-kind-mismatch-if Γ "computed" kₑ? KdStar) -]
  return-when (TpIota x T₁~ T₂~) KdStar

-- {^ T ^} (generated by theta)
check-type Γ (ExTpNoSpans T pi) kₑ? = check-type Γ T kₑ? ≫=spand spanMr

-- [d] - T
check-type Γ (ExTpLet pi d T) kₑ? =
  check-let Γ d ff (type-start-pos T) (type-end-pos T) ≫=span λ where
    (Γ' , x , tv , σ , f) →
      case-ret-body {m = kₑ?} (check-type Γ' T kₑ?) λ T~ k~ →
      [- punctuation-span "Parens (let)" pi (type-end-pos T) -]
      [- TpLet-span pi (type-end-pos T) (maybe-to-checking kₑ?)
           (maybe-else' kₑ? (kind-data Γ k~) (expected-kind Γ) :: [ tv ]) -]
      return-when (σ T~) (σ k~)

-- T T'
check-type Γ (ExTpApp T T') kₑ? =
  Γ ⊢ T ↝ T~ ⇒ kₕ /
  Γ ⊢ kₕ =β= λ where
    (KdAbs x (Tkk dom) cod) →
      Γ ⊢ T' ⇐ dom ↝ T'~ /
      [- TpApp-span (type-start-pos T) (type-end-pos T) (maybe-to-checking kₑ?)
           (kind-data Γ cod :: expected-kind-if Γ kₑ?)
           (check-for-kind-mismatch-if Γ "synthesized" kₑ? cod) -]
      return-when (TpApp T~ (Ttp T'~)) cod
    kₕ' →
      [- TpApp-span (type-start-pos T) (type-end-pos T') (maybe-to-checking kₑ?)
           (head-kind Γ kₕ' :: expected-kind-if Γ kₑ?)
           (just ("The synthesized kind of the head does not allow it to be applied" ^
                  "to a type argument")) -]
      return-when (TpHole (type-start-pos T')) KdStar

-- T t
check-type Γ (ExTpAppt T t) kₑ? =
  Γ ⊢ T ↝ T~ ⇒ kₕ /
  Γ ⊢ kₕ =β= λ where
    (KdAbs x (Tkt dom) cod) →
      Γ ⊢ t ⇐ dom ↝ t~ /
      [- TpAppt-span (type-start-pos T) (term-end-pos t) (maybe-to-checking kₑ?)
           (kind-data Γ cod :: expected-kind-if Γ kₑ?)
           (check-for-kind-mismatch-if Γ "synthesized" kₑ? cod) -]
      return-when (TpApp T~ (Ttm t~)) cod
    kₕ' →
      [- TpAppt-span (type-start-pos T) (term-end-pos t) (maybe-to-checking kₑ?)
           (head-kind Γ kₕ' :: expected-kind-if Γ kₑ?)
           (just ("The synthesized kind of the head does not allow it to be applied" ^
                  "to a term argument")) -]
      return-when (TpHole (term-start-pos t)) KdStar

-- T ➔ T'
check-type Γ (ExTpArrow T e T') kₑ? =
  Γ ⊢ T ⇐ KdStar ↝ T~ /
  Γ ⊢ T' ⇐ KdStar ↝ T'~ /
  [- TpArrow-span T T' (maybe-to-checking kₑ?)
       (kind-data Γ KdStar :: expected-kind-if Γ kₑ?)
       (check-for-kind-mismatch-if Γ "computed" kₑ? KdStar) -]
  return-when (TpAbs e ignored-var (Tkt T~) T'~) KdStar

-- { t₁ ≃ t₂ }
check-type Γ (ExTpEq pi t₁ t₂ pi') kₑ? =
  untyped-term Γ t₁ ≫=span t₁~ /
  untyped-term Γ t₂ ≫=span t₂~ /
  [- punctuation-span "Parens (equation)" pi pi' -]
  [- TpEq-span pi pi' (maybe-to-checking kₑ?)
       (kind-data Γ KdStar :: expected-kind-if Γ kₑ?)
       (check-for-kind-mismatch-if Γ "computed" kₑ? KdStar) -]
  return-when (TpEq t₁~ t₂~) KdStar

-- ●
check-type Γ (ExTpHole pi) kₑ? =
  [- tp-hole-span Γ pi kₑ? (expected-kind-if Γ kₑ?) -]
  return-when (TpHole pi) KdStar

-- λ x : tk. T
check-type Γ (ExTpLam pi pi' x tk T) kₑ? =
  [- punctuation-span "Lambda (type)" pi (posinfo-plus pi 1) -]
  Γ ⊢ tk ↝ tk~ /
  case-ret
    (Γ ⊢ T ↝ T~ ⇒ k /
     let kₛ = KdAbs x tk~ (rename-var Γ (pi' % x) x k) in
     [- TpLambda-span Γ pi pi' x tk~ T synthesizing [ kind-data Γ kₛ ] nothing -]
     spanMr2 (TpLam x tk~ (rename-var Γ (pi' % x) x T~)) kₛ)
    λ kₑ →
      (Γ ⊢ kₑ =β= λ where
        (KdAbs x' tk' k) →
          (Γ , pi' - x :` tk~) ⊢ T ⇐ (rename-var Γ x' x k) ↝ T~ /
          spanMr (rename-var Γ (pi' % x) x T~ , lambda-bound-conv? Γ x tk' tk~ [])
        KdStar →
          (Γ , pi' - x :` Tkt (TpHole pi')) ⊢ T ↝ T~ ⇒ _ /
          spanMr (rename-var Γ (pi' % x) x T~ , [] , just
              "The expected kind is not an arrow- or Pi-kind")
      ) ≫=span λ where
        (T~ , tvs , e?) →
          [- TpLambda-span Γ pi pi' x tk~ T checking (expected-kind Γ kₑ :: tvs) e? -]
          spanMr (TpLam x tk~ T~)

-- (T)
check-type Γ (ExTpParens pi T pi') kₑ? =
  [- punctuation-span "Parens (type)" pi pi' -]
  check-type Γ T kₑ?

-- x
check-type Γ (ExTpVar pi x) kₑ? =
  maybe-else' (ctxt-lookup-type-var Γ x)
    ([- TpVar-span Γ pi x (maybe-to-checking kₑ?) (expected-kind-if Γ kₑ?)
          (just "Undefined type variable") -]
     return-when (TpHole pi) KdStar)
    λ {(qx , as , k) →
      [- TpVar-span Γ pi x (maybe-to-checking kₑ?)
           (expected-kind-if Γ kₑ? ++ [ kind-data Γ k ])
           (check-for-kind-mismatch-if Γ "computed" kₑ? k) -]
      return-when (apps-type (TpVar qx) as) k}
  


-- Π x : tk. k
check-kind Γ (ExKdAbs pi pi' x tk k) =
  Γ ⊢ tk ↝ tk~ /
  Γ , pi' - x :` tk~ ⊢ k ↝ k~ /
  [- KdAbs-span Γ pi pi' x tk~ k checking nothing -]
  [- punctuation-span "Pi (kind)" pi (posinfo-plus pi 1) -]
  spanMr (KdAbs x tk~ ([ Γ - Var x / (pi' % x)] k~))

-- tk ➔ k
check-kind Γ (ExKdArrow tk k) =
  Γ ⊢ tk ↝ tk~ /
  Γ ⊢ k ↝ k~ /
  [- KdArrow-span tk k checking nothing -]
  spanMr (KdAbs ignored-var tk~ k~)

-- (k)
check-kind Γ (ExKdParens pi k pi') =
  [- punctuation-span "Parens (kind)" pi pi' -]
  check-kind Γ k

-- ★
check-kind Γ (ExKdStar pi) =
  [- Star-span pi checking nothing -]
  spanMr KdStar

-- κ as...
check-kind Γ (ExKdVar pi κ as) =
  case ctxt-lookup-kind-var-def Γ κ of λ where
    nothing →
      [- KdVar-span Γ (pi , κ) (args-end-pos (posinfo-plus-str pi κ) as) [] checking []
           (just "Undefined kind variable") -]
      spanMr KdStar -- TODO: Maybe make a "KdHole"?
    (just (ps , k)) →
      check-args Γ as ps ≫=span λ as~ →
      [- KdVar-span Γ (pi , κ) (args-end-pos (posinfo-plus-str pi κ) as) ps checking (params-data Γ ps) (maybe-if (length as < length ps) ≫maybe just ("Needed " ^ ℕ-to-string (length ps ∸ length as) ^ " further argument(s)")) -]
      spanMr (fst (subst-params-args' Γ ps as~ k))


check-tpkd Γ (ExTkt T) =
  check-type Γ T (just KdStar) ≫=span T~ /
  spanMr (Tkt T~)

check-tpkd Γ (ExTkk k) =  
  check-kind Γ k ≫=span k~ /
  spanMr (Tkk k~)

check-args Γ (ExTmArg me t :: as) (Param me' x (Tkt T) :: ps) =
  Γ ⊢ t ⇐ T ↝ t~ /
  let e-s = mk-span "Argument" (term-start-pos t) (term-end-pos t)
              [ expected-type Γ T ] (just "Mismatched argument erasure") 
      e-m = λ r → if me iff me' then spanMr r else ([- e-s -] spanMr r) in
  check-args Γ as (subst-params Γ t~ x ps) ≫=span λ as~ →
  e-m ((if me then inj₂ (inj₁ t~) else inj₁ t~) :: as~)
check-args Γ (ExTpArg T :: as) (Param _ x (Tkk k) :: ps) =
  Γ ⊢ T ⇐ k ↝ T~ /
  check-args Γ as (subst-params Γ T~ x ps) ≫=span λ as~ →
  spanMr (inj₂ (inj₂ T~) :: as~)
check-args Γ (ExTmArg me t :: as) (Param _ x (Tkk k) :: ps) =
  [- mk-span "Argument" (term-start-pos t) (term-end-pos t) [ expected-kind Γ k ]
       (just "Expected a type argument") -]
  spanMr []
check-args Γ (ExTpArg T :: as) (Param me x (Tkt T') :: ps) =
  [- mk-span "Argument" (type-start-pos T) (type-end-pos T) [ expected-type Γ T' ]
       (just ("Expected a" ^ (if me then "n erased" else "") ^ " term argument")) -]
  spanMr []
check-args Γ (a :: as) [] =
  let range = case a of λ {(ExTmArg me t) → term-start-pos t , term-end-pos t;
                           (ExTpArg T) → type-start-pos T , type-end-pos T} in
  check-args Γ as [] ≫=span λ as~ →
  [- mk-span "Argument" (fst range) (snd range) [] (just "Too many arguments given") -]
  spanMr []
check-args Γ [] _ = spanMr []

check-let Γ (ExDefTerm pi x (just Tₑ) t) e? fm to =
  Γ ⊢ Tₑ ⇐ KdStar ↝ Tₑ~ /
  Γ ⊢ t ⇐ Tₑ~ ↝ t~ /
  elim-pair (compileFail-in Γ t~) λ tvs e → 
  [- Var-span Γ pi x checking (type-data Γ Tₑ~ :: tvs) e -]
  spanMr
    (ctxt-term-def pi localScope opacity-open x (just t~) Tₑ~ Γ ,
     pi % x ,
     binder-data Γ pi x (Tkt Tₑ~) e? (just t~) fm to ,
     (λ {ed} T' → [ Γ - t~ / (pi % x) ] T') ,
     (λ t' → LetTm e? x nothing t~ ([ Γ - Var x / (pi % x) ] t')))
check-let Γ (ExDefTerm pi x nothing t) e? fm to =
  Γ ⊢ t ↝ t~ ⇒ Tₛ~ /
  elim-pair (compileFail-in Γ t~) λ tvs e →
  [- Var-span Γ pi x synthesizing (type-data Γ Tₛ~ :: tvs) e -]
  spanMr
    (ctxt-term-def pi localScope opacity-open x (just t~) Tₛ~ Γ ,
     pi % x ,
     binder-data Γ pi x (Tkt Tₛ~) e? (just t~) fm to ,
     (λ {ed} T' → [ Γ - t~ / (pi % x) ] T') ,
     (λ t' → LetTm e? x nothing t~ ([ Γ - Var x / (pi % x) ] t')))
check-let Γ (ExDefType pi x k T) e? fm to =
  Γ ⊢ k ↝ k~ /
  Γ ⊢ T ⇐ k~ ↝ T~ /
  [- TpVar-span Γ pi x checking [ kind-data Γ k~ ] nothing -]
  spanMr
    (ctxt-type-def pi localScope opacity-open x (just T~) k~ Γ ,
     pi % x ,
     binder-data Γ pi x (Tkk k~) e? (just T~) fm to ,
     (λ {ed} T' → [ Γ - T~ / (pi % x) ] T') ,
     (λ t' → LetTp x k~ T~ ([ Γ - TpVar x / (pi % x) ] t')))



untyped-term Γ t = spanMr (Hole pi-gen)
untyped-type Γ T = spanMr (TpHole pi-gen)
untyped-kind Γ k = spanMr KdStar
untyped-tpkd Γ (ExTkt T) = untyped-type Γ T ≫=span λ T~ → spanMr (Tkt T~)
untyped-tpkd Γ (ExTkk k) = untyped-kind Γ k ≫=span λ k~ → spanMr (Tkk k~)
