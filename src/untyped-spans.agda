import cedille-options
open import general-util

module untyped-spans (options : cedille-options.options) {F : Set → Set} {{monadF : monad F}} where

open import lib
open import ctxt
open import cedille-types
open import constants
open import conversion
open import free-vars
open import spans options {F}
open import subst
open import syntax-util
open import to-string options
open import type-util

{-# TERMINATING #-}
untyped-term : ctxt → ex-tm → spanM term
untyped-type : ctxt → ex-tp → spanM type
untyped-kind : ctxt → ex-kd → spanM kind
untyped-tpkd : ctxt → ex-tk → spanM tpkd
untyped-arg : ctxt → ex-arg → spanM arg
untyped-args : ctxt → ex-args → spanM args
untyped-let : ctxt → ex-def → erased? → posinfo → posinfo → spanM (ctxt × var × tagged-val × (∀ {ed : exprd} → ⟦ ed ⟧ → ⟦ ed ⟧) × (term → term))
untyped-cases : ctxt → ex-cases → spanM (cases × 𝕃 tagged-val × err-m)


untyped-let Γ (ExDefTerm pi x Tₑ? t) e? fm to =
  maybe-map (untyped-type Γ) Tₑ? ≫=span? λ Tₑ?~ →
  untyped-term Γ t ≫=span λ t~ →
  elim-pair (compileFail-in Γ t~) λ tvs e →
  [- Var-span Γ pi x untyped tvs e -]
  let Tₑ~ = maybe-else' Tₑ?~ (TpHole pi) id in
  spanMr
    (ctxt-term-def pi localScope opacity-open x (just t~) Tₑ~ Γ ,
     pi % x ,
     binder-data Γ pi x (Tkt Tₑ~) e? (just t~) fm to ,
     (λ {ed} T' → [ Γ - t~ / (pi % x) ] T') ,
     (λ t' → LetTm e? x nothing t~ ([ Γ - Var x / (pi % x) ] t')))
untyped-let Γ (ExDefType pi x k T) e? fm to =
  untyped-kind Γ k ≫=span λ k~ →
  untyped-type Γ T ≫=span λ T~ →
  [- TpVar-span Γ pi x untyped [] nothing -]
  spanMr
    (ctxt-type-def pi localScope opacity-open x (just T~) k~ Γ ,
     pi % x ,
     binder-data Γ pi x (Tkk k~) e? (just T~) fm to ,
     (λ {ed} T' → [ Γ - T~ / (pi % x) ] T') ,
     (λ t' → LetTp x k~ T~ ([ Γ - TpVar x / (pi % x) ] t')))

untyped-term Γ (ExApp t e t') =
  [- App-span ff (term-start-pos t) (term-end-pos t') untyped [] nothing -]
  untyped-term Γ t ≫=span λ t~ →
  untyped-term Γ t' ≫=span λ t'~ →
  spanMr (if e then t~ else App t~ t'~)
untyped-term Γ (ExAppTp t T) =
  [- AppTp-span (term-start-pos t) (type-end-pos T) untyped [] nothing -]
  untyped-type Γ T ≫=span λ T~ →
  untyped-term Γ t
untyped-term Γ (ExBeta pi t? t?') =
  maybe-map (λ {(PosTm t pi) → untyped-term Γ t}) t? ≫=span? λ t?~ →
  maybe-map (λ {(PosTm t pi) → untyped-term Γ t}) t?' ≫=span? λ t?'~ →
  [- Beta-span pi (term-end-pos (ExBeta pi t? t?')) untyped [] nothing -]
  spanMr (maybe-else' t?'~ id-term id)
untyped-term Γ (ExChi pi T? t) =
  maybe-map (untyped-type Γ) T? ≫=span? λ T?~ →
  [- Chi-span Γ pi T?~ t untyped [] nothing -]
  untyped-term Γ t
untyped-term Γ (ExDelta pi T? t) =
  [- Delta-span pi t untyped [] nothing -]
  maybe-map (untyped-type Γ) T? ≫=span? λ T?~ →
  untyped-term Γ t ≫=span λ t~ →
  spanMr id-term
untyped-term Γ (ExEpsilon pi lr -? t) =
  [- Epsilon-span pi lr -? t untyped [] nothing -]
  untyped-term Γ t
untyped-term Γ (ExHole pi) =
  [- hole-span Γ pi nothing untyped [] -]
  spanMr (Hole pi)
untyped-term Γ (ExIotaPair pi t₁ t₂ Tₘ? pi') =
  let tv-f = λ {(ExGuide pi'' x Tₘ) →
               [ binder-data Γ pi'' x (Tkt (TpHole pi'')) ff nothing
                   (type-start-pos Tₘ) (type-end-pos Tₘ) ]} in
  [- IotaPair-span pi pi' untyped (maybe-else' Tₘ? [] tv-f) nothing -]
  untyped-term Γ t₁ ≫=span λ t₁~ →
  untyped-term Γ t₂ ≫=span λ t₂~ →
  maybe-map (λ {(ExGuide pi'' x Tₘ) →
    untyped-type (ctxt-term-decl pi'' x (TpHole pi'') Γ) Tₘ}) Tₘ? ≫=span? λ Tₘ?~ →
  spanMr t₁~
untyped-term Γ (ExIotaProj t n pi) =
  [- IotaProj-span t pi untyped [] nothing -]
  untyped-term Γ t
untyped-term Γ (ExLam pi e pi' x tk? t) =
  (spanMr tk? on-fail spanMr (Tkt (TpHole pi')) ≫=spanm' untyped-tpkd Γ) ≫=span λ tk~ →
  untyped-term (ctxt-tk-decl pi' x tk~ Γ) t ≫=span λ t~ →
  let eₖ? = tk? ≫=maybe λ _ → maybe-if (tk-is-type tk~ && ~ e) ≫maybe
                just "λ-terms must bind a term, not a type (use Λ instead)"
      eₑ? = maybe-if (e && is-free-in x (erase t~)) ≫maybe
                just "The Λ-bound variable occurs free in the erasure of the body" in
  [- Lam-span Γ untyped pi pi' e x tk~ t [] (eₖ? maybe-or eₑ?) -]
  spanMr (if e then t~ else Lam ff x nothing t~)
untyped-term Γ (ExLet pi e? d t) =
  untyped-let Γ d e? (term-start-pos t) (term-end-pos t) ≫=span λ where
    (Γ' , x , tv , σ , f) →
      untyped-term Γ' t ≫=span λ t~ →
      [- punctuation-span "Parens (let)" pi (term-end-pos t) -]
      [- Let-span e? pi (term-end-pos t) untyped []
           (maybe-if (e? && is-free-in x t~) ≫maybe
            just (unqual-local x ^ "occurs free in the body of the term")) -]
      spanMr (if is-free-in x t~ then f t~ else t~)
untyped-term Γ (ExOpen pi o pi' x t) =
  [- Var-span Γ pi' x untyped [ not-for-navigation ] nothing -]
  [- Open-span o pi x t untyped [] nothing -]
  untyped-term Γ t
untyped-term Γ (ExParens pi t pi') =
  [- punctuation-span "Parens (term)" pi pi' -]
  untyped-term Γ t
untyped-term Γ (ExPhi pi t₌ t₁ t₂ pi') =
  [- Phi-span pi pi' untyped [] nothing -]
  untyped-term Γ t₌ ≫span
  untyped-term Γ t₁ ≫span
  untyped-term Γ t₂
untyped-term Γ (ExRho pi ρ+? ρ<ns>? t₌ Tₘ? t) =
  [- Rho-span pi t₌ t untyped ρ+?
       (maybe-else' Tₘ? (inj₁ 1) λ {(ExGuide pi' x Tₘ) → inj₂ x}) [] nothing -]
  untyped-term Γ t₌ ≫span
  maybe-map (λ {(ExGuide pi' x Tₘ) →
                  untyped-type (ctxt-var-decl-loc pi' x Γ) Tₘ}) Tₘ? ≫=span? λ Tₘ?~ →
  untyped-term Γ t
untyped-term Γ (ExSigma pi t) =
  [- Sigma-span pi t untyped [] nothing -]
  untyped-term Γ t
untyped-term Γ (ExTheta pi θ t ts) =
  [- Theta-span Γ pi θ t ts untyped [] nothing -]
  untyped-term Γ t ≫=span λ t~ →
  untyped-args Γ (map (λ {(Lterm e t) → ExTmArg e t}) ts) ≫=span λ as~ →
  spanMr (recompose-apps (map Arg (erase-args as~)) t~)
untyped-term Γ (ExMu pi μ t Tₘ? pi' ms pi'') = -- TODO
  untyped-term Γ t {- ≫=span λ t~ →
  -- [- Mu-span Γ pi (just x) pi''' (optType-elim ot nothing just) untyped ts e -]
  spanMr Tₘ? on-fail spanMr (TpHole pi) ≫=spanm' untyped-type Γ ≫=span? λ Tₘ~ →
  (case μ of λ where
    (ExIsMu pi''' x) →
      [- Var-span Γ pi''' x untyped [] nothing -]
      let Γ' = ctxt-term-decl pi''' x (Tkt Tₘ~) Γ in
      spanMr (Γ' , [ binder-data Γ' pi''' x Tₘ~ ff nothing pi' pi'' ])
    (ExIsMu' t?) →
      maybe-
      spanMr) ≫=spanc λ Γ' tvs →
  ?-}
untyped-term Γ (ExVar pi x) =
  maybe-else' (ctxt-binds-term-var Γ x)
    ([- Var-span Γ pi x untyped [] (just "Not a term variable") -]
    spanMr (Hole pi))
    λ {(qx , as) →
      [- Var-span Γ pi x untyped [] nothing -]
      spanMr (recompose-apps (map Arg (erase-args as)) (Var qx))}


-- ∀/Π x : tk. T
untyped-type Γ (ExTpAbs pi e pi' x tk T) =
  untyped-tpkd Γ tk ≫=span λ tk~ →
  untyped-type (Γ , pi' - x :` tk~) T ≫=span λ T~ →
  let T~ = rename-var Γ (pi' % x) x T~ in
  [- punctuation-span "Forall" pi (posinfo-plus pi 1) -]
  [- TpQuant-span Γ e pi pi' x tk~ T untyped [] nothing -]
  spanMr (TpAbs e x tk~ T~)

-- ι x : T₁. T₂
untyped-type Γ (ExTpIota pi pi' x T₁ T₂) =
  untyped-type Γ T₁ ≫=span λ T₁~ →
  untyped-type (Γ , pi' - x :` Tkt T₁~) T₂ ≫=span λ T₂~ →
  let T₂~ = rename-var Γ (pi' % x) x T₂~ in
  [- punctuation-span "Forall" pi (posinfo-plus pi 1) -]
  [- Iota-span Γ pi pi' x T₂~ T₂ untyped [] nothing -]
  spanMr (TpIota x T₁~ T₂~)

-- {^ T ^} (generated by theta)
untyped-type Γ (ExTpNoSpans T pi) = untyped-type Γ T ≫=spand spanMr

-- [d] - T
untyped-type Γ (ExTpLet pi d T) =
  untyped-let Γ d ff (type-start-pos T) (type-end-pos T) ≫=span λ where
    (Γ' , x , tv , σ , f) →
      untyped-type Γ' T ≫=span λ T~ →
      [- punctuation-span "Parens (let)" pi (type-end-pos T) -]
      [- TpLet-span pi (type-end-pos T) untyped [ tv ] -]
      spanMr (σ T~)

-- T · T'
untyped-type Γ (ExTpApp T T') =
  untyped-type Γ T ≫=span λ T~ →
  untyped-type Γ T' ≫=span λ T'~ →
  [- TpApp-span (type-start-pos T) (type-end-pos T) untyped [] nothing -]
  spanMr (TpApp T~ (Ttp T'~))

-- T t
untyped-type Γ (ExTpAppt T t) =
  untyped-type Γ T ≫=span λ T~ →
  untyped-term Γ t ≫=span λ t~ →
  [- TpAppt-span (type-start-pos T) (term-end-pos t) untyped [] nothing -]
  spanMr (TpApp T~ (Ttm t~))

-- T ➔/➾ T'
untyped-type Γ (ExTpArrow T e T') =
  untyped-type Γ T ≫=span λ T~ →
  untyped-type Γ T' ≫=span λ T'~ →
  [- TpArrow-span T T' untyped [] nothing -]
  spanMr (TpAbs e ignored-var (Tkt T~) T'~)

-- { t₁ ≃ t₂ }
untyped-type Γ (ExTpEq pi t₁ t₂ pi') =
  untyped-term Γ t₁ ≫=span λ t₁~ →
  untyped-term Γ t₂ ≫=span λ t₂~ →
  [- punctuation-span "Parens (equation)" pi pi' -]
  [- TpEq-span pi pi' untyped [] nothing -]
  spanMr (TpEq t₁~ t₂~)

-- ●
untyped-type Γ (ExTpHole pi) =
  [- tp-hole-span Γ pi nothing untyped [] -]
  spanMr (TpHole pi)

-- λ x : tk. T
untyped-type Γ (ExTpLam pi pi' x tk T) =
  untyped-tpkd Γ tk ≫=span λ tk~ →
  untyped-type (Γ , pi' - x :` tk~) T ≫=span λ T~ →
  [- punctuation-span "Lambda (type)" pi (posinfo-plus pi 1) -]
  [- TpLambda-span Γ pi pi' x tk~ T untyped [] nothing -]
  spanMr (TpLam x tk~ (rename-var Γ (pi' % x) x T~))

-- (T)
untyped-type Γ (ExTpParens pi T pi') =
  [- punctuation-span "Parens (type)" pi pi' -]
  untyped-type Γ T

-- x
untyped-type Γ (ExTpVar pi x) =
  maybe-else' (ctxt-binds-type-var Γ x)
    ([- TpVar-span Γ pi x untyped [] (just "Undefined type variable") -]
     spanMr (TpHole pi))
    λ {(qx , as) →
      [- TpVar-span Γ pi x untyped [] nothing -]
      spanMr (apps-type (TpVar qx) (erase-args-keep as))}


-- Π x : tk. k
untyped-kind Γ (ExKdAbs pi pi' x tk k) =
  untyped-tpkd Γ tk ≫=span λ tk~ →
  untyped-kind (Γ , pi' - x :` tk~) k ≫=span λ k~ →
  [- KdAbs-span Γ pi pi' x tk~ k untyped nothing -]
  [- punctuation-span "Pi (kind)" pi (posinfo-plus pi 1) -]
  spanMr (KdAbs x tk~ ([ Γ - Var x / (pi' % x)] k~))

-- tk ➔ k
untyped-kind Γ (ExKdArrow tk k) =
  untyped-tpkd Γ tk ≫=span λ tk~ →
  untyped-kind Γ k ≫=span λ k~ →
  [- KdArrow-span tk k untyped nothing -]
  spanMr (KdAbs ignored-var tk~ k~)

-- (k)
untyped-kind Γ (ExKdParens pi k pi') =
  [- punctuation-span "Parens (kind)" pi pi' -]
  untyped-kind Γ k

-- ★
untyped-kind Γ (ExKdStar pi) =
  [- Star-span pi untyped nothing -]
  spanMr KdStar

-- κ as...
untyped-kind Γ (ExKdVar pi κ as) =
  case ctxt-lookup-kind-var-def Γ κ of λ where
    nothing →
      [- KdVar-span Γ (pi , κ) (args-end-pos (posinfo-plus-str pi κ) as) [] untyped []
           (just "Undefined kind variable") -]
      spanMr KdStar -- TODO: Maybe make a "KdHole"?
    (just (ps , k)) →
      untyped-args Γ as ≫=span λ as~ →
      ([- KdVar-span Γ (pi , κ)
            (args-end-pos (posinfo-plus-str pi κ) as) ps untyped (params-data Γ ps)
            (maybe-if (length as < length ps) ≫maybe
             just ("Needed " ^ ℕ-to-string (length ps ∸ length as) ^
                     " further argument(s)")) -]
      spanMr (fst (subst-params-args' Γ ps as~ k)))

untyped-arg Γ (ExTmArg e? t) =
  untyped-term Γ t ≫=span λ t →
  spanMr (if e? then inj₂ (inj₁ t) else inj₁ t)
untyped-arg Γ (ExTpArg T) =
  untyped-type Γ T ≫=span λ T →
  spanMr (inj₂ (inj₂ T))

untyped-args Γ as =
  spanM-for map (untyped-arg Γ) as
    init spanMr []
    use λ a as → as ≫=span λ as → spanMr (a :: as)

untyped-tpkd Γ (ExTkt T) = untyped-type Γ T ≫=span λ T~ → spanMr (Tkt T~)
untyped-tpkd Γ (ExTkk k) = untyped-kind Γ k ≫=span λ k~ → spanMr (Tkk k~)

untyped-cases Γ ms = spanMr ([] , [] , nothing) -- TODO
