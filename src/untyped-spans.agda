import cedille-options
open import general-util

module untyped-spans (options : cedille-options.options) {F : Set → Set} ⦃ monadF : monad F ⦄ where

open import ctxt
open import cedille-types
open import constants
open import conversion
open import free-vars
open import rename
open import spans options {F} ⦃ monadF ⦄
open import subst
open import syntax-util
open import to-string options
open import type-util
open import elab-util options

{-# TERMINATING #-}
untyped-term : ctxt → ex-tm → spanM term
untyped-type : ctxt → ex-tp → spanM type
untyped-kind : ctxt → ex-kd → spanM kind
untyped-tpkd : ctxt → ex-tk → spanM tpkd
untyped-arg : ctxt → ex-arg → spanM arg
untyped-args : ctxt → ex-args → spanM args
untyped-let : ctxt → ex-def → erased? → posinfo → posinfo → spanM (ctxt × var × tagged-val × (∀ {ed : exprd} → ⟦ ed ⟧ → ⟦ ed ⟧) × (term → term))
untyped-cases : ctxt → ex-cases → renamectxt → spanM cases
untyped-case : ctxt → ex-case → (siblings : ℕ) → (ℕ → err-m) → renamectxt → spanM (case × (ℕ → err-m) × maybe ℕ)

untyped-let Γ (ExDefTerm pi x Tₑ? t) e? fm to =
  maybe-map (untyped-type Γ) Tₑ? >>=? λ Tₑ?~ →
  untyped-term Γ t >>= λ t~ →
  elim-pair (compileFail-in Γ t~) λ tvs e →
  let Tₑ~ = maybe-else' Tₑ?~ (TpHole pi) id in
  [- Var-span (Γ , pi - x :` Tkt Tₑ~) pi x untyped tvs e -]
  return
    (ctxt-term-def pi localScope opacity-open x (just t~) Tₑ~ Γ ,
     pi % x ,
     binder-data Γ pi x (Tkt Tₑ~) e? (just t~) fm to ,
     (λ {ed} T' → [ Γ - t~ / (pi % x) ] T') ,
     (λ t' → LetTm e? x nothing t~ ([ Γ - Var x / (pi % x) ] t')))

untyped-let Γ (ExDefType pi x k T) e? fm to =
  untyped-kind Γ k >>= λ k~ →
  untyped-type Γ T >>= λ T~ →
  [- TpVar-span (Γ , pi - x :` Tkk k~) pi x untyped [] nothing -]
  return
    (ctxt-type-def pi localScope opacity-open x (just T~) k~ Γ ,
     pi % x ,
     binder-data Γ pi x (Tkk k~) e? (just T~) fm to ,
     (λ {ed} T' → [ Γ - T~ / (pi % x) ] T') ,
     (λ t' → LetTp x k~ T~ ([ Γ - TpVar x / (pi % x) ] t')))


untyped-term Γ (ExApp t e t') =
  [- App-span tt (term-start-pos t) (term-end-pos t') untyped [] nothing -]
  untyped-term Γ t >>= λ t~ →
  untyped-term Γ t' >>= λ t'~ →
  return (if e then t~ else App t~ t'~)

untyped-term Γ (ExAppTp t T) =
  [- AppTp-span tt (term-start-pos t) (type-end-pos T) untyped [] nothing -]
  untyped-type Γ T >>= λ T~ →
  untyped-term Γ t

untyped-term Γ (ExBeta pi t? t?') =
  maybe-map (λ {(PosTm t pi) → untyped-term Γ t}) t? >>=? λ t?~ →
  maybe-map (λ {(PosTm t pi) → untyped-term Γ t}) t?' >>=? λ t?'~ →
  [- Beta-span pi (term-end-pos (ExBeta pi t? t?')) untyped [] nothing -]
  return (maybe-else' t?'~ id-term id)

untyped-term Γ (ExChi pi T? t) =
  maybe-map (untyped-type Γ) T? >>=? λ T?~ →
  [- Chi-span Γ pi T?~ t untyped [] nothing -]
  untyped-term Γ t

untyped-term Γ (ExDelta pi T? t) =
  [- Delta-span pi t untyped [] nothing -]
  maybe-map (untyped-type Γ) T? >>=? λ T?~ →
  untyped-term Γ t >>= λ t~ →
  return id-term

untyped-term Γ (ExEpsilon pi lr -? t) =
  [- Epsilon-span pi lr -? t untyped [] nothing -]
  untyped-term Γ t

untyped-term Γ (ExHole pi) =
  [- hole-span Γ pi nothing untyped [] -]
  return (Hole pi)

untyped-term Γ (ExIotaPair pi t₁ t₂ Tₘ? pi') =
  let tv-f = λ {(ExGuide pi'' x Tₘ) →
               [ binder-data Γ pi'' x (Tkt (TpHole pi'')) ff nothing
                   (type-start-pos Tₘ) (type-end-pos Tₘ) ]} in
  [- IotaPair-span pi pi' untyped (maybe-else' Tₘ? [] tv-f) nothing -]
  untyped-term Γ t₁ >>= λ t₁~ →
  untyped-term Γ t₂ >>= λ t₂~ →
  maybe-map (λ {(ExGuide pi'' x Tₘ) →
    untyped-type (ctxt-term-decl pi'' x (TpHole pi'') Γ) Tₘ}) Tₘ? >>=? λ Tₘ?~ →
  return t₁~

untyped-term Γ (ExIotaProj t n pi) =
  [- IotaProj-span t pi untyped [] nothing -]
  untyped-term Γ t

untyped-term Γ (ExLam pi e pi' x tk? t) =
  (return tk? on-fail return (Tkt (TpHole pi')) >>=m untyped-tpkd Γ) >>= λ tk~ →
  untyped-term (Γ , pi' - x :` tk~) t >>= λ t~ →
  let eₖ? = tk? >>= λ _ → maybe-if (tk-is-type tk~ && ~ e) >>
                just "λ-terms must bind a term, not a type (use Λ instead)"
      eₑ? = maybe-if (e && is-free-in (pi' % x) (erase t~)) >>
                just "The Λ-bound variable occurs free in the erasure of the body" in
  [- var-span e (Γ , pi' - x :` tk~) pi' x untyped tk~ eₑ? -]
  [- Lam-span Γ untyped pi pi' e x tk~ t [] eₖ? -]
  return (if e then t~ else Lam ff x nothing ([ Γ - Var x / (pi' % x) ] t~))

untyped-term Γ (ExLet pi e? d t) =
  untyped-let Γ d e? (term-start-pos t) (term-end-pos t) >>= λ where
    (Γ' , x , tv , σ , f) →
      untyped-term Γ' t >>= λ t~ →
      [- punctuation-span "Parens (let)" pi (term-end-pos t) -]
      [- Let-span e? pi (term-end-pos t) untyped []
           (maybe-if (e? && is-free-in x t~) >>
            just (unqual-local x ^ "occurs free in the body of the term")) -]
      return (if is-free-in x t~ then f t~ else t~)

untyped-term Γ (ExOpen pi o pi' x t) =
  [- Var-span Γ pi' x untyped [ not-for-navigation ] nothing -]
  [- Open-span o pi x t untyped [] nothing -]
  untyped-term Γ t

untyped-term Γ (ExParens pi t pi') =
  [- punctuation-span "Parens (term)" pi pi' -]
  untyped-term Γ t

untyped-term Γ (ExPhi pi t₌ t₁ t₂ pi') =
  [- Phi-span pi pi' untyped [] nothing -]
  untyped-term Γ t₌ >>
  untyped-term Γ t₁ >>
  untyped-term Γ t₂

untyped-term Γ (ExRho pi ρ+? ρ<ns>? t₌ Tₘ? t) =
  [- Rho-span pi t₌ t untyped ρ+?
       (maybe-else' Tₘ? (inj₁ 1) λ {(ExGuide pi' x Tₘ) → inj₂ x}) [] nothing -]
  untyped-term Γ t₌ >>
  maybe-map (λ {(ExGuide pi' x Tₘ) →
                  untyped-type (ctxt-var-decl-loc pi' x Γ) Tₘ}) Tₘ? >>=? λ Tₘ?~ →
  untyped-term Γ t

untyped-term Γ (ExSigma pi t) =
  [- Sigma-span pi t untyped [] nothing -]
  untyped-term Γ t

untyped-term Γ (ExTheta pi θ t ts) =
  [- Theta-span Γ pi θ t ts untyped [] nothing -]
  untyped-term Γ t >>= λ t~ →
  untyped-args Γ (map (λ {(Lterm e t) → ExTmArg e t}) ts) >>= λ as~ →
  return (recompose-apps (map Arg (erase-args as~)) t~)

untyped-term Γ (ExMu pi μ t Tₘ? pi' ms pi'') =
  untyped-term Γ t >>= λ t~ →
  maybe-map (untyped-type Γ) Tₘ? >>=? λ Tₘ~? →
  (case_of_ {B = spanM (ctxt × renamectxt × is-mu × 𝕃 tagged-val)} μ λ where
    (ExIsMu pi''' x) →
      [- Var-span Γ pi''' x untyped [] nothing -]
      let Γ' = ctxt-term-decl pi''' x (TpHole pi''') Γ in
      return (Γ' , renamectxt-single (pi''' % x) x , inj₂ x ,
               [ binder-data Γ' pi''' x (Tkt (TpHole pi''')) ff nothing pi' pi'' ])
    (ExIsMu' t?) →
      maybe-map (untyped-term Γ) t? >>=? λ t~? →
      return (Γ , empty-renamectxt , inj₁ t~? , []))
  >>= λ where
    (Γ' , ρ , μ~ , tvs) →
      untyped-cases Γ' ms ρ >>= λ ms~ →
      -- Make sure we aren't matching upon a "False" datatype (e.g., one
      -- with no constructors) before any datatypes have been declared
      maybe-else' (head2 (trie-mappings (ctxt.μ Γ)))
        ([- Mu-span Γ pi μ pi'' Tₘ~? untyped tvs
              (just "No datatypes have been declared yet") -]
         return (Hole pi))
        λ where
          (Dₓ , ps , kᵢ , k , cs , eds , ecs) →
            [- Mu-span Γ pi μ pi'' Tₘ~? untyped tvs nothing -]
            return (Mu μ~ t~ nothing (mk-data-info Dₓ Dₓ (params-to-args ps) [] ps kᵢ k cs cs eds ecs) ms~)

-- x
untyped-term Γ (ExVar pi x) =
  maybe-else' (ctxt-binds-term-var Γ x)
    ([- Var-span Γ pi x untyped [] (just "Not a term variable") -]
    return (Var x))
    λ {(qx , as) →
      [- Var-span Γ pi x untyped [] nothing -]
      return (recompose-apps (map Arg (erase-args as)) (Var qx))}


-- ∀/Π x : tk. T
untyped-type Γ (ExTpAbs pi e pi' x tk T) =
  untyped-tpkd Γ tk >>= λ tk~ →
  untyped-type (Γ , pi' - x :` tk~) T >>= λ T~ →
  let T~ = rename-var Γ (pi' % x) x T~ in
  [- punctuation-span "Forall" pi (posinfo-plus pi 1) -]
  [- var-span e (Γ , pi' - x :` tk~) pi' x untyped tk~ nothing -]
  [- TpQuant-span Γ e pi pi' x tk~ T untyped [] nothing -]
  return (TpAbs e x tk~ T~)

-- ι x : T₁. T₂
untyped-type Γ (ExTpIota pi pi' x T₁ T₂) =
  untyped-type Γ T₁ >>= λ T₁~ →
  untyped-type (Γ , pi' - x :` Tkt T₁~) T₂ >>= λ T₂~ →
  let T₂~ = rename-var Γ (pi' % x) x T₂~ in
  [- punctuation-span "Forall" pi (posinfo-plus pi 1) -]
  [- var-span ff (Γ , pi' - x :` Tkt T₁~) pi' x untyped (Tkt T₁~) nothing -]
  [- Iota-span Γ pi pi' x T₂~ T₂ untyped [] nothing -]
  return (TpIota x T₁~ T₂~)

-- {^ T ^} (generated by theta)
untyped-type Γ (ExTpNoSpans T pi) = untyped-type Γ T >>=spand return

-- [d] - T
untyped-type Γ (ExTpLet pi d T) =
  untyped-let Γ d ff (type-start-pos T) (type-end-pos T) >>= λ where
    (Γ' , x , tv , σ , f) →
      untyped-type Γ' T >>= λ T~ →
      [- punctuation-span "Parens (let)" pi (type-end-pos T) -]
      [- TpLet-span pi (type-end-pos T) untyped [ tv ] -]
      return (σ T~)

-- T · T'
untyped-type Γ (ExTpApp T T') =
  untyped-type Γ T >>= λ T~ →
  untyped-type Γ T' >>= λ T'~ →
  [- TpApp-span (type-start-pos T) (type-end-pos T) untyped [] nothing -]
  return (TpAppTp T~ T'~)

-- T t
untyped-type Γ (ExTpAppt T t) =
  untyped-type Γ T >>= λ T~ →
  untyped-term Γ t >>= λ t~ →
  [- TpAppt-span (type-start-pos T) (term-end-pos t) untyped [] nothing -]
  return (TpAppTm T~ t~)

-- T ➔/➾ T'
untyped-type Γ (ExTpArrow T e T') =
  untyped-type Γ T >>= λ T~ →
  untyped-type Γ T' >>= λ T'~ →
  [- TpArrow-span T T' untyped [] nothing -]
  return (TpAbs e ignored-var (Tkt T~) T'~)

-- { t₁ ≃ t₂ }
untyped-type Γ (ExTpEq pi t₁ t₂ pi') =
  untyped-term Γ t₁ >>= λ t₁~ →
  untyped-term Γ t₂ >>= λ t₂~ →
  [- punctuation-span "Parens (equation)" pi pi' -]
  [- TpEq-span pi pi' untyped [] nothing -]
  return (TpEq t₁~ t₂~)

-- ●
untyped-type Γ (ExTpHole pi) =
  [- tp-hole-span Γ pi nothing untyped [] -]
  return (TpHole pi)

-- λ x : tk. T
untyped-type Γ (ExTpLam pi pi' x tk T) =
  untyped-tpkd Γ tk >>= λ tk~ →
  untyped-type (Γ , pi' - x :` tk~) T >>= λ T~ →
  [- punctuation-span "Lambda (type)" pi (posinfo-plus pi 1) -]
  [- var-span ff (Γ , pi' - x :` tk~) pi' x untyped tk~ nothing -]
  [- TpLambda-span Γ pi pi' x tk~ T untyped [] nothing -]
  return (TpLam x tk~ (rename-var Γ (pi' % x) x T~))

-- (T)
untyped-type Γ (ExTpParens pi T pi') =
  [- punctuation-span "Parens (type)" pi pi' -]
  untyped-type Γ T

-- x
untyped-type Γ (ExTpVar pi x) =
  maybe-else' (ctxt-binds-type-var Γ x)
    ([- TpVar-span Γ pi x untyped [] (just "Undefined type variable") -]
     return (TpVar x))
    λ {(qx , as) →
      [- TpVar-span Γ pi x untyped [] nothing -]
      return (apps-type (TpVar qx) (erase-args-keep as))}


-- Π x : tk. k
untyped-kind Γ (ExKdAbs pi pi' x tk k) =
  untyped-tpkd Γ tk >>= λ tk~ →
  untyped-kind (Γ , pi' - x :` tk~) k >>= λ k~ →
  [- KdAbs-span Γ pi pi' x tk~ k untyped nothing -]
  [- var-span ff (Γ , pi' - x :` tk~) pi' x untyped tk~ nothing -]
  [- punctuation-span "Pi (kind)" pi (posinfo-plus pi 1) -]
  return (KdAbs x tk~ (rename-var Γ (pi' % x) x k~))

-- tk ➔ k
untyped-kind Γ (ExKdArrow tk k) =
  untyped-tpkd Γ tk >>= λ tk~ →
  untyped-kind Γ k >>= λ k~ →
  [- KdArrow-span tk k untyped nothing -]
  return (KdAbs ignored-var tk~ k~)

-- ●
untyped-kind Γ (ExKdHole pi) =
  [- kd-hole-span pi untyped -]
  return (KdHole pi)

-- (k)
untyped-kind Γ (ExKdParens pi k pi') =
  [- punctuation-span "Parens (kind)" pi pi' -]
  untyped-kind Γ k

-- ★
untyped-kind Γ (ExKdStar pi) =
  [- Star-span pi untyped nothing -]
  return KdStar

-- κ as...
untyped-kind Γ (ExKdVar pi κ as) =
  case ctxt-lookup-kind-var-def Γ κ of λ where
    nothing →
      [- KdVar-span Γ (pi , κ) (args-end-pos (posinfo-plus-str pi κ) as) [] untyped []
           (just "Undefined kind variable") -]
      return (KdHole pi)
    (just (ps , k)) →
      untyped-args Γ as >>= λ as~ →
      [- KdVar-span Γ (pi , κ)
           (args-end-pos (posinfo-plus-str pi κ) as)
           ps untyped (params-data Γ ps)
           (unless (length as =ℕ length ps)
             ("Expected " ^ ℕ-to-string (length ps) ^
              " argument" ^ (if length ps =ℕ 1 then "" else "s") ^
              ", but got " ^ ℕ-to-string (length as))) -]
      return (fst (subst-params-args' Γ ps as~ k))

untyped-arg Γ (ExTmArg ff t) = inj₁ <$> untyped-term Γ t
untyped-arg Γ (ExTmArg tt t) = (inj₂ ∘ inj₁) <$> untyped-term Γ t
untyped-arg Γ (ExTpArg T) = (inj₂ ∘ inj₂) <$> untyped-type Γ T

untyped-args Γ = sequenceA ∘ map (untyped-arg Γ)

untyped-tpkd Γ (ExTkt T) = Tkt <$> untyped-type Γ T
untyped-tpkd Γ (ExTkk k) = Tkk <$> untyped-kind Γ k

untyped-cases Γ ms ρ =
  let msₗ = length ms in
  foldl (λ m rec ms f → untyped-case Γ m msₗ f ρ >>= uncurry₂ λ m asₗ n? → rec (maybe-else' n? ms (λ n → set-nth n (just m) ms)) asₗ)
    (const ∘ return) ms (repeat (length ms) nothing) (λ _ → nothing) >>=r drop-nothing

untyped-case-args : ctxt → posinfo → ex-case-args → ex-tm → renamectxt → spanM (case-args × term)
untyped-case-args Γ pi cas t ρ =
  foldr {B = ctxt → renamectxt → 𝕃 tagged-val → (term → spanM ⊤) → spanM (case-args × term)}
    (λ {(ExCaseArg me pi x) rec Γ' ρ tvs sm →
      let tk = case me of λ {ExCaseArgTp → Tkk (KdHole pi-gen);
                             ExCaseArgTm → Tkt (TpHole pi-gen);
                             ExCaseArgEr → Tkt (TpHole pi-gen)} in
      rec
        (ctxt-tk-decl pi x tk Γ')
        (renamectxt-insert ρ (pi % x) x)
        (binder-data Γ' pi x tk (ex-case-arg-erased me) nothing
          (term-start-pos t) (term-end-pos t) :: tvs)
        (λ t →
          [- var-span (ex-case-arg-erased me) Γ' pi x untyped tk
            (when (ex-case-arg-erased me && is-free-in (pi % x) (erase t))
              "The bound variable occurs free in the erasure of the body (not allowed)") -]
          sm t) >>=c λ cas →
      return2 (case me of λ {ExCaseArgTm → CaseArg ff x nothing :: cas; _ → cas})})
    (λ Γ' ρ tvs sm →
      [- pattern-clause-span pi t (reverse tvs) -]
      untyped-term Γ' t >>= λ t~ →
      sm t~ >>
      return2 [] (subst-renamectxt Γ' ρ t~))
    cas Γ ρ [] λ _ → spanMok

untyped-case Γ (ExCase pi x cas t) csₗ asₗ ρ =
  untyped-case-args Γ pi cas t ρ >>=c λ cas~ t~ →
  case (qual-lookup Γ x) of λ where
    (just (qx , as , ctr-def ps T Cₗ cᵢ cₐ , loc)) →
      let c~ = Case qx cas~ t~ []
          eᵢ = "This constructor overlaps with " ^ x
          eₐ = unless (length cas~ =ℕ cₐ)
                 ("Expected " ^ ℕ-to-string cₐ ^
                  " arguments after erasure, but got " ^ ℕ-to-string (length cas~))
          eₗ = unless (Cₗ =ℕ csₗ)
                 ("Constructor's datatype has " ^ ℕ-to-string Cₗ ^
                  (if Cₗ =ℕ 1 then " constructor" else " constructors") ^
                  ", but expected " ^ ℕ-to-string csₗ) in
      [- Var-span Γ pi x untyped [] (asₗ cᵢ ||-maybe (eₐ ||-maybe eₗ)) -]
      return2 c~ ((λ cᵢ' → when (cᵢ =ℕ cᵢ') eᵢ) , (maybe-not (asₗ cᵢ) >> just cᵢ))
    _ →
      [- Var-span Γ pi x untyped [] (just $ "This is not a valid constructor name") -]
      return2 (Case x cas~ t~ []) (asₗ , nothing)
