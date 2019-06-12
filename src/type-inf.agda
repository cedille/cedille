open import lib
open import cedille-types
import spans
open import ctxt
import cedille-options
open import general-util

module type-inf
  (options : cedille-options.options)
  {mF : Set → Set}
  {{_ : monad mF}}
  (check-term : ctxt → ex-tm → (T? : maybe type) → spans.spanM options {mF} (spans.check-ret options {mF} T? term))
  (check-type : ctxt → ex-tp → (k? : maybe kind) → spans.spanM options {mF} (spans.check-ret options {mF} k? type)) where

open import spans options {mF}
open import rename
open import syntax-util
open import type-util
open import meta-vars options {mF}
open import resugar
open import subst
open import conversion
open import free-vars

record spine-data : Set where
  constructor mk-spine-data
  field
    spine-mvars : meta-vars
    spine-type : decortype
    spine-locale : ℕ
    spine-elab : args → args × term

check-term-spine-elim : ctxt → spine-data → term × type
check-term-spine-elim Γ (mk-spine-data Xs dt locl f~) =
  elim-pair (maybe-else' (meta-vars-to-args Xs) ([] , Hole pi-gen) f~) recompose-apps ,
  meta-vars-subst-type' ff Γ Xs (decortype-to-type dt)

check-term-spine : ctxt → ex-tm → (m : prototype) → 𝔹 → spanM (maybe spine-data)

check-term-spine-return : meta-vars → decortype → ℕ → (args → args × term) → spanM (maybe spine-data)
check-term-spine-return Xs dt locl f~ = spanMr (just (mk-spine-data Xs dt locl f~))

-- a flag indicating how aggresively we should be unfolding during matching.
-- "both" is the backtracking flag. We will attempt "both" matches, which means
-- first matching without unfolding, then if that fails unfolding the type once
-- and continue matching the subexpresions with "both"
data match-unfolding-state : Set where
  match-unfolding-both match-unfolding-approx match-unfolding-hnf : match-unfolding-state

-- main matching definitions
-- --------------------------------------------------

-- NOTE: these functions don't actually ever emit spans
match-types : ctxt → meta-vars → local-vars → match-unfolding-state → (tpₓ tp : type) → spanM $ match-error-t meta-vars
match-kinds : ctxt → meta-vars → local-vars → match-unfolding-state → (kₓ k : kind) → spanM $ match-error-t meta-vars
match-tpkds : ctxt → meta-vars → local-vars → match-unfolding-state → (tkₓ tk : tpkd) → spanM $ match-error-t meta-vars

record match-prototype-data : Set where
  constructor mk-match-prototype-data
  field
    match-proto-mvars : meta-vars
    match-proto-dectp : decortype
    match-proto-error : 𝔹
open match-prototype-data
match-prototype : ctxt → (Xs : meta-vars) (is-hnf : 𝔹) (tp : type) (pt : prototype) → spanM $ match-prototype-data

-- substitutions used during matching
-- --------------------------------------------------

-- These have to be in the spanM monad because substitution can unlock a `stuck`
-- decoration, causing another round of prototype matching (which invokes type matching)

substh-decortype : ctxt → renamectxt → trie (Σi exprd ⟦_⟧) → decortype → spanM $ decortype
substh-decortype Γ ρ σ (decor-type tp) = spanMr $ decor-type (substh Γ ρ σ tp)
substh-decortype Γ ρ σ (decor-arrow e? dom cod) =
  substh-decortype Γ ρ σ cod
  ≫=span λ cod → spanMr $ decor-arrow e? (substh Γ ρ σ dom) cod
  -- spanMr $ decor-arrow e? (substh-type Γ ρ σ dom) (substh-decortype Γ ρ σ cod)
substh-decortype Γ ρ σ (decor-decor e? x tk sol dt) =
  let x' = subst-rename-var-if Γ ρ x σ
      Γ' = ctxt-var-decl x' Γ
      ρ' = renamectxt-insert ρ x x'
  in substh-decortype Γ' ρ' σ dt
  ≫=span λ dt' → spanMr $ decor-decor e? x' (substh Γ ρ σ -tk tk) (substh-meta-var-sort Γ ρ σ sol) dt'
  -- decor-decor e? x' (substh-meta-var-sol Γ' ρ' σ sol) (substh-decortype Γ' ρ' σ dt)
substh-decortype Γ ρ σ (decor-stuck tp pt) =
  match-prototype Γ meta-vars-empty ff (substh Γ ρ σ tp) pt
  -- NOTE: its an invariant that if you start with no meta-variables, prototype matching
  -- produces no meta-variables as output
  ≫=span λ ret → spanMr (match-proto-dectp ret)

substh-decortype Γ ρ σ (decor-error tp pt) =
  spanMr $ decor-error (substh Γ ρ σ tp) pt

subst-decortype : {ed : exprd} → ctxt → ⟦ ed ⟧ → var → decortype → spanM decortype
subst-decortype Γ s x dt = substh-decortype Γ empty-renamectxt (trie-single x (, s)) dt

meta-vars-subst-decortype' : (unfold : 𝔹) → ctxt → meta-vars → decortype → spanM decortype
meta-vars-subst-decortype' uf Γ Xs dt =
  substh-decortype Γ empty-renamectxt (meta-vars-get-sub Xs) dt
  ≫=span λ dt' → spanMr $
    if uf then hnf-decortype Γ unfold-head-elab dt' tt else dt'

meta-vars-subst-decortype : ctxt → meta-vars → decortype → spanM decortype
meta-vars-subst-decortype = meta-vars-subst-decortype' tt


-- unfolding a decorated type to reveal a term / type abstraction
-- --------------------------------------------------

{-# TERMINATING #-}
meta-vars-peel' : ctxt → span-location → meta-vars → decortype → spanM $ (𝕃 meta-var) × decortype
meta-vars-peel' Γ sl Xs (decor-decor e? x _ (meta-var-tp k mtp) dt) =
  let Y   = meta-var-fresh-tp Xs x sl (k , mtp)
      Xs' = meta-vars-add Xs Y
  in subst-decortype Γ (meta-var-to-type-unsafe Y) x dt
  ≫=span λ dt' → meta-vars-peel' Γ sl Xs' dt'
  ≫=span λ ret → let Ys = fst ret ; rdt = snd ret
  in spanMr $ Y :: Ys , rdt
meta-vars-peel' Γ sl Xs dt@(decor-decor e? x _ (meta-var-tm _ _) _) = spanMr $ [] , dt
meta-vars-peel' Γ sl Xs dt@(decor-arrow _ _ _) = spanMr $ [] , dt
-- NOTE: vv The clause below will later generate a type error vv
meta-vars-peel' Γ sl Xs dt@(decor-stuck _ _) = spanMr $ [] , dt
-- NOTE: vv The clause below is an internal error, if reached vv
meta-vars-peel' Γ sl Xs dt@(decor-type _) = spanMr $ [] , dt
meta-vars-peel' Γ sl Xs dt@(decor-error _ _) = spanMr $ [] , dt

meta-vars-unfold-tmapp' : ctxt → span-location → meta-vars → decortype → spanM $ (𝕃 meta-var × is-tmabsd?)
meta-vars-unfold-tmapp' Γ sl Xs dt =
  meta-vars-subst-decortype Γ Xs dt
  ≫=span λ dt' → meta-vars-peel' Γ sl Xs dt'
  ≫=span λ where
    (Ys , dt'@(decor-arrow e? dom cod)) →
      spanMr $ Ys , yes-tmabsd dt' e? "_" dom ff cod
    (Ys , dt'@(decor-decor e? x _ (meta-var-tm dom _) cod)) →
      spanMr $ Ys , yes-tmabsd dt' e? x dom (is-free-in x (decortype-to-type cod)) cod
    (Ys , dt@(decor-decor _ _ _ (meta-var-tp _ _) _)) →
      spanMr $ Ys , not-tmabsd dt
-- NOTE: vv this is a type error vv
    (Ys , dt@(decor-stuck _ _)) →
      spanMr $ Ys , not-tmabsd dt
-- NOTE: vv this is an internal error, if reached vv
    (Ys , dt@(decor-type _)) →
      spanMr $ Ys , not-tmabsd dt
    (Ys , dt@(decor-error _ _)) →
      spanMr $ Ys , not-tmabsd dt

meta-vars-unfold-tpapp' : ctxt → meta-vars → decortype → spanM is-tpabsd?
meta-vars-unfold-tpapp' Γ Xs dt =
  meta-vars-subst-decortype Γ Xs dt
  ≫=span λ where
   (dt″@(decor-decor e? x _ (meta-var-tp k mtp) dt')) →
    spanMr $ yes-tpabsd dt″ e? x k (flip maybe-map mtp meta-var-sol.sol) dt'
   (dt″@(decor-decor _ _ _ (meta-var-tm _ _) _)) →
    spanMr $ not-tpabsd dt″
   (dt″@(decor-arrow _ _ _)) → spanMr $ not-tpabsd dt″
   (dt″@(decor-stuck _ _)) → spanMr $ not-tpabsd dt″
   (dt″@(decor-type _)) → spanMr $ not-tpabsd dt″
   (dt″@(decor-error _ _)) → spanMr $ not-tpabsd dt″



-- errors
-- --------------------------------------------------

-- general type errors for applications
module check-term-app-tm-errors
  {A : Set} (t₁ t₂ : ex-tm) (htp : type) (Xs : meta-vars) (is-locale : 𝔹) (m : checking-mode) (Γ : ctxt)
  where

  inapplicable : erased? → decortype → prototype → spanM (maybe A)
  inapplicable e? dt pt =
    spanM-add
      (App-span is-locale (term-start-pos t₁) (term-end-pos t₂) m
        (head-type Γ (meta-vars-subst-type Γ Xs htp)
          -- :: decortype-data Γ dt
          -- :: prototype-data Γ pt
          :: meta-vars-data-all Γ Xs)
        (just $ "The type of the head does not allow the head to be applied to "
         ^ h e? ^ " argument"))
    ≫span spanMr nothing
    where h : erased? → string
          h Erased = "an erased term"
          h NotErased = "a term"

  bad-erasure : erased? → spanM (maybe A)
  bad-erasure e? =
    spanM-add
      (App-span is-locale (term-start-pos t₁) (term-end-pos t₂) m
        (head-type Γ (meta-vars-subst-type Γ Xs htp) :: meta-vars-data-all Γ Xs)
        (just (msg e?)))
    ≫span spanMr nothing
    where
    msg : erased? → string
    msg Erased =
      "The type computed for the head requires an explicit (non-erased) argument,"
      ^ " but the application is marked as erased"
    msg NotErased =
      "The type computed for the head requires an implicit (erased) argument,"
      ^ " but the application is marked as not erased"

  unmatchable : (tpₓ tp : type) (msg : string) → 𝕃 tagged-val → spanM (maybe A)
  unmatchable tpₓ tp msg tvs =
    spanM-add
      (App-span is-locale (term-start-pos t₁) (term-end-pos t₂) m
        (arg-exp-type Γ tpₓ :: arg-type Γ tp :: tvs ++ meta-vars-data-all Γ Xs)
        (just msg))
    ≫span spanMr nothing

  unsolved-meta-vars : type → 𝕃 tagged-val → spanM (maybe A)
  unsolved-meta-vars tp tvs =
    spanM-add
      (App-span tt (term-start-pos t₁) (term-end-pos t₂) m
        (type-data Γ tp :: meta-vars-data-all Γ Xs ++ tvs)
        (just "There are unsolved meta-variables in this maximal application"))
    ≫span spanMr nothing

module check-term-app-tp-errors
  {A : Set} (t : ex-tm) (tp : ex-tp) (htp : type) (Xs : meta-vars) (m : checking-mode) (Γ : ctxt)
  where

  inapplicable : decortype → spanM (maybe A)
  inapplicable dt =
    spanM-add
      (AppTp-span tt (term-start-pos t) (type-end-pos tp) synthesizing
        (head-type Γ (meta-vars-subst-type Γ Xs htp)
          -- :: decortype-data Γ dt
          :: meta-vars-data-all Γ Xs)
        (just "The type of the head does not allow the head to be applied to a type argument"))
    ≫span spanMr nothing

  ctai-disagree : (ctai-sol : type) → spanM $ maybe A
  ctai-disagree ctai-sol =
    spanM-add (AppTp-span tt (term-start-pos t) (type-end-pos tp) m
      (head-type Γ (meta-vars-subst-type Γ Xs htp)
        :: contextual-type-argument Γ ctai-sol
        :: meta-vars-data-all Γ Xs)
      (just "The given and contextually inferred type argument differ"))
    ≫span spanMr nothing

-- meta-variable locality
-- --------------------------------------------------

-- for debugging -- prepend to the tvs returned by check-spine-locality if you're having trouble
private
  locale-tag : ℕ → tagged-val
  locale-tag n = "locale n" , [[ ℕ-to-string n ]] , []

private
  is-locale : (max : 𝔹) → (locl : maybe ℕ) → 𝔹
  is-locale max locl = max || maybe-else' locl ff iszero

check-spine-locality : ctxt → meta-vars → type → (max : 𝔹) → (locl : ℕ)
                       → spanM (maybe (meta-vars × ℕ × 𝔹))
check-spine-locality Γ Xs tp max locl =
  let new-locl  = if iszero locl then num-arrows-in-type Γ tp else locl
      new-Xs    = if iszero locl then meta-vars-empty else Xs
      left-locl = is-locale max (just locl)
  in if left-locl && (~ meta-vars-solved? Xs)
        then spanMr nothing
     else spanMr (just (new-Xs , new-locl , left-locl))


-- main definition
--------------------------------------------------

data check-term-app-ret : Set where
  check-term-app-return : (t~ : term) (Xs : meta-vars) (cod : decortype) (arg-mode : checking-mode) → (tvs : 𝕃 tagged-val) → check-term-app-ret

check-term-app : ctxt → (Xs : meta-vars) (Ys : 𝕃 meta-var) → (t₁ t₂ : ex-tm) → is-tmabsd → 𝔹 → spanM (maybe check-term-app-ret)

check-term-spine Γ t'@(ExApp t₁ e? t₂) pt max =
  -- 1) type the applicand, extending the prototype
    let pt' = proto-arrow NotErased pt in
    check-term-spine Γ t₁ pt' ff
      on-fail handleApplicandTypeError
  -- 2) make sure the applicand type reveals an arrow (term abstraction)
  ≫=spanm' λ ret → let (mk-spine-data Xs dt locl fₕ~) = ret in
    -- the meta-vars need to know the span they were introduced in
    let sloc = span-loc $ ctxt-get-current-filename Γ in
    -- see if the decorated type of the head `dt` reveals an arrow
    meta-vars-unfold-tmapp' Γ sloc Xs dt
  ≫=spanc λ Ys tm-arrow? →
    spanMr tm-arrow? on-fail (λ _ → genInapplicableError Xs dt pt' locl)
    -- if so, get the (plain, undecorated) type of the head `htp`
  ≫=spans' λ arr → let htp = decortype-to-type ∘ is-tmabsd-dt $ arr in
  -- 3) make sure erasures of the applicand type + syntax of application match
    checkErasuresMatch e? (is-tmabsd-e? arr) htp Xs locl
  -- 4) type the application, filling in missing type arguments with meta-variables
  ≫=spanm' λ _ → check-term-app Γ Xs Ys t₁ t₂ arr (islocl locl)
  -- 5) check no unsolved mvars, if the application is maximal (or a locality)
  ≫=spanm' λ {(check-term-app-return t₂~ Xs' rtp' arg-mode tvs) →
    let rtp = decortype-to-type rtp' in
    checkLocality Γ Xs' htp rtp max (pred locl) tvs
  ≫=spanm' uncurry₂ λ Xs'' locl' is-loc →
  -- 6) generate span
    genAppSpan Γ Xs Xs' Ys pt rtp is-loc tvs
  ≫span check-term-spine-return Xs'' rtp' locl'
  -- 7) fill in solutions to meta-vars introduced here and return the rest
    λ sols →
      elim-pair (fₕ~ sols) λ sols tₕₓ~ →
      let num-sols-here = length Ys
          sols-here = take num-sols-here sols
          sols-rest = drop num-sols-here sols
          tₕ~ = recompose-apps sols-here tₕₓ~ in
      sols-rest , if e? then AppE tₕ~ (Ttm t₂~) else App tₕ~ t₂~
  }

  where
  mode = prototype-to-checking pt

  expected-type-if-pt : ctxt → prototype → 𝕃 tagged-val
  expected-type-if-pt Γ pt = case pt of λ where
    (proto-maybe mt) → maybe-else [] (λ tp → [ expected-type Γ tp ]) mt
    (proto-arrow _ _) → []

  span-loc : (fn : string) → span-location
  span-loc fn = fn , term-start-pos t₁ , term-end-pos t₂

  islocl : ℕ → 𝔹
  islocl locl = is-locale max (just $ pred locl)

  handleApplicandTypeError : spanM ∘ maybe $ _
  handleApplicandTypeError =
      spanM-add (App-span max (term-start-pos t₁) (term-end-pos t₂) mode (expected-type-if-pt Γ pt) nothing)
    ≫span check-term Γ t₂ nothing
    ≫=span (const $ spanMr nothing)

  genInapplicableError : meta-vars → decortype → prototype → (locl : ℕ) → spanM (maybe _)
  genInapplicableError Xs dt pt locl =
    check-term-app-tm-errors.inapplicable
      t₁ t₂ (decortype-to-type dt) Xs (islocl locl) mode Γ e? dt (proto-arrow e? pt)

  checkErasuresMatch : (e?₁ e?₂ : erased?) → type → meta-vars → (locl : ℕ) → spanM ∘ maybe $ ⊤
  checkErasuresMatch e?₁ e?₂ htp Xs locl =
    if e?₁ xor e?₂
      then check-term-app-tm-errors.bad-erasure t₁ t₂ htp Xs (islocl locl) mode Γ e?₁
    else (spanMr ∘ just $ triv)

  checkLocality : ctxt → meta-vars → (htp rtp : type) → (max : 𝔹) (locl : ℕ) → 𝕃 tagged-val → spanM ∘ maybe $ _
  checkLocality Γ Xs htp rtp max locl tvs =
    check-spine-locality Γ Xs rtp max locl
      on-fail check-term-app-tm-errors.unsolved-meta-vars
        t₁ t₂ htp Xs (islocl locl) mode Γ rtp tvs
    ≫=spanm' (spanMr ∘ just)

  genAppSpan : ctxt → (Xs Xs' : meta-vars) → (Ys : 𝕃 meta-var) → prototype → type → (is-locl : 𝔹) → 𝕃 tagged-val → spanM ⊤
  genAppSpan Γ Xs Xs' Ys pt rtp is-loc tvs =
    spanM-add $ elim-pair
      (meta-vars-check-type-mismatch-if (prototype-to-maybe pt) Γ "synthesized" meta-vars-empty rtp)
      λ tvs' → App-span is-loc (term-start-pos t₁) (term-end-pos t₂) mode
        (tvs' ++ meta-vars-intro-data Γ (meta-vars-from-list Ys)
          ++ meta-vars-sol-data Γ Xs Xs' ++ tvs)

check-term-spine Γ t'@(ExAppTp t tp) pt max =
  -- 1) type the applicand
    check-term-spine Γ t pt max
      on-fail handleApplicandTypeError
  ≫=spanm' λ ret → let (mk-spine-data Xs dt locl fₕ~) = ret ; htp = decortype-to-type dt in
  -- 2) make sure it reveals a type abstraction
    meta-vars-unfold-tpapp' Γ Xs dt
     on-fail (λ _ → genInapplicableError Xs htp dt)
  -- 3) ensure the type argument has the expected kind,
  --    but don't compare with the contextually infered type argument (for now)
  ≫=spans' λ ret → let mk-tpabsd dt e? x k sol rdt = ret in
    check-type Γ tp (just (meta-vars-subst-kind Γ Xs k))
  -- 4) produce the result type of the application
  ≫=span λ tp~ → subst-decortype-if Γ tp~ Xs x k sol rdt
  ≫=span λ ret → let Xs = fst ret ; rdt = snd ret ; rtp = decortype-to-type rdt in
  -- 5) generate span data
    genAppTpSpan Γ Xs pt rtp
  ≫span check-term-spine-return Xs rdt locl
  -- 7) fill in solutions to meta-vars introduced here and return the rest
    (map-snd (λ tₕ~ → AppE tₕ~ (Ttp tp~)) ∘ fₕ~)

  where
  mode = prototype-to-checking pt

  span-loc : ctxt → span-location
  span-loc Γ = (ctxt-get-current-filename Γ) , term-start-pos t , type-end-pos tp

  handleApplicandTypeError : spanM ∘ maybe $ spine-data
  handleApplicandTypeError =
      [- AppTp-span tt (term-start-pos t) (type-end-pos tp) synthesizing [] nothing -]
    check-type Γ tp nothing ≫=span λ _ → spanMr nothing

  genInapplicableError : meta-vars → type → decortype → spanM ∘ maybe $ spine-data
  genInapplicableError Xs htp dt =
    check-term-app-tp-errors.inapplicable t tp htp Xs mode Γ dt

  subst-decortype-if : ctxt → type → meta-vars → var → kind → maybe type → decortype → spanM (meta-vars × decortype)
  subst-decortype-if Γ tp Xs x k sol rdt =
    if ~ is-hole tp
      then subst-decortype Γ tp x rdt ≫=span (λ res → spanMr (Xs , res))
      else let sol = maybe-map (λ t → mk-meta-var-sol t checking) sol
               Y   = meta-var-fresh-tp Xs x (span-loc Γ) (k , sol)
               Xs' = meta-vars-add Xs Y
           in subst-decortype Γ (meta-var-to-type-unsafe Y) x rdt ≫=span λ rdt' → spanMr (Xs' , rdt')

  genAppTpSpan : ctxt → meta-vars → prototype → (ret-tp : type) → spanM ⊤
  genAppTpSpan Γ Xs pt ret-tp = spanM-add ∘ elim-pair
    -- check for a type mismatch, if there even is an expected type
    (meta-vars-check-type-mismatch-if (prototype-to-maybe pt) Γ "synthesizing" Xs ret-tp) $
    -- then take the generated 𝕃 tagged-val and add to the span
    λ tvs → AppTp-span ff (term-start-pos t) (type-end-pos tp) mode $ tvs ++ meta-vars-data-all Γ Xs -- ++ (prototype-data Γ tp :: [ decortype-data Γ dt ])

check-term-spine Γ (ExParens _ t _) pt max =
  check-term-spine Γ t pt max

check-term-spine Γ t pt max =
  check-term Γ t nothing ≫=spanc λ t~ htp →
  let locl = num-arrows-in-type Γ htp
  in match-prototype Γ meta-vars-empty ff htp pt
  -- NOTE: it is an invariant that the variables solved in the
  -- solution set of the fst of this are a subset of the variables given
  -- to match-* -- that is, for (σ , W) = match-prototype ...
  -- we have dom(σ) = ∅
  ≫=span λ ret → let dt = match-proto-dectp ret in
  check-term-spine-return meta-vars-empty dt locl (_, t~)

-- check-term-app
-- --------------------------------------------------
--
-- If `dom` has unsolved meta-vars in it, synthesize argument t₂ and try to solve for them.
-- Otherwise, check t₂ against a fully known expected type
check-term-app Γ Xs Zs t₁ t₂ (mk-tmabsd dt e? x dom occurs cod) is-locl =
   let Xs' = meta-vars-add* Xs Zs ; tp = decortype-to-type dt in
  -- 1) either synth or check arg type, depending on available info
  --    checking "exits early", as well as failure
  checkArgWithMetas Xs' tp (genAppRetType Γ)
    exit-early spanMr
  -- 2) match *synthesized* type with expected (partial) type
  ≫=spans' uncurry₂ λ rdt t₂~ atp → match-types Γ Xs' empty-trie match-unfolding-both dom atp
  ≫=span (handleMatchResult Xs' t₂~ atp tp rdt)

  where
  mode = synthesizing

  genAppRetType : ctxt → term → spanM decortype
  genAppRetType Γ t₂~ = if occurs then subst-decortype Γ t₂~ x cod else spanMr cod

  genAppRetTypeHole : ctxt → spanM decortype
  genAppRetTypeHole Γ = if occurs then subst-decortype Γ (Hole posinfo-gen) x cod else spanMr cod

  checkArgWithMetas : meta-vars → type → (term → spanM decortype) → spanM (maybe check-term-app-ret ∨ (decortype × term × type))
  checkArgWithMetas Xs' tp rdt-f =
    -- check arg against fully known type
    if ~ meta-vars-are-free-in-type Xs' dom
      then (check-term Γ t₂ (just dom) ≫=span λ t₂~ →
            rdt-f t₂~ ≫=span λ rdt →
            spanMr (inj₁ (just $ check-term-app-return t₂~ Xs' rdt mode [])))
    -- synthesize type for the argument
      else (check-term Γ t₂ nothing ≫=spanc λ t tp →
            rdt-f t ≫=span λ rdt →
            spanMr (inj₂ $ rdt , t , tp))

  handleMatchResult : meta-vars → (t₂~ : term) → (atp tp : type) → decortype → match-error-t meta-vars → spanM ∘ maybe $ check-term-app-ret
  handleMatchResult Xs' t₂~ atp tp rdt (match-error (msg , tvs)) =
    check-term-app-tm-errors.unmatchable
      t₁ t₂ tp Xs' is-locl mode Γ dom atp msg tvs
  handleMatchResult Xs' t₂~ atp tp rdt (match-ok Xs) =
      meta-vars-subst-decortype' ff Γ Xs rdt
    ≫=span λ rdt → spanMr ∘ just $ check-term-app-return t₂~ Xs rdt mode []

match-unfolding-next : match-unfolding-state → match-unfolding-state
match-unfolding-next match-unfolding-both = match-unfolding-both
match-unfolding-next match-unfolding-approx = match-unfolding-approx
match-unfolding-next match-unfolding-hnf = match-unfolding-both

module m-err = meta-vars-match-errors

check-type-for-match : ctxt → type → spanM $ match-error-t kind
check-type-for-match Γ tp =
  (with-clear-error $
      check-type (qualified-ctxt Γ) (resugar tp) nothing ≫=spanc λ _ k → spanMr (match-ok $ k)) ≫=spand spanMr

-- match-types
-- --------------------------------------------------

match-types-ok : meta-vars → spanM $ match-error-t meta-vars
match-types-ok = spanMr ∘ match-ok

match-types-error : match-error-data → spanM $ match-error-t meta-vars
match-types-error = spanMr ∘ match-error

match-types Γ Xs Ls match-unfolding-both tpₓ tp =
    match-types Γ Xs Ls match-unfolding-approx tpₓ tp
  ≫=span λ where
    (match-ok Xs) → match-types-ok Xs
    (match-error msg) →
      match-types Γ Xs Ls match-unfolding-hnf
        (hnf Γ unfold-head-elab tpₓ)
        (hnf Γ unfold-head-elab tp)

match-types Γ Xs Ls unf tpₓ@(TpVar x) tp =
  -- check that x is a meta-var
  maybe-else' (meta-vars-lookup-with-kind Xs x)
    -- if not, make sure the two variables are the same
    -- TODO: above assumes no term meta-variables
    (spanMr (err⊎-guard (~ conv-type Γ tpₓ tp) m-err.e-match-failure
            ≫⊎ match-ok Xs))
  -- scope check the solution
  λ ret → let X = fst ret ; kₓ = snd ret in
  if are-free-in Ls tp then
    match-types-error $ m-err.e-meta-scope Γ tpₓ tp
  else (check-type-for-match Γ tp
  ≫=spans' λ k → match-kinds Γ Xs empty-trie match-unfolding-both kₓ k
    on-fail (λ _ → spanMr ∘ match-error $ m-err.e-bad-sol-kind Γ x tp)
  ≫=spans' λ Xs → spanMr (meta-vars-solve-tp Γ Xs x tp synthesizing)
  ≫=spans' λ Xs → match-types-ok $ meta-vars-update-kinds Γ Xs Xs)

match-types Γ Xs Ls unf (TpApp tpₓ₁ (Ttp tpₓ₂)) (TpApp tp₁ (Ttp tp₂)) =
    match-types Γ Xs Ls unf tpₓ₁ tp₁
  ≫=spans' λ Xs' → match-types Γ Xs' Ls (match-unfolding-next unf) tpₓ₂ tp₂

match-types Γ Xs Ls unf (TpApp tpₓ (Ttm tmₓ)) (TpApp tp (Ttm tm)) =
    match-types Γ Xs Ls unf tpₓ tp
  ≫=spans' λ Xs' →
    spanMr $ if ~ conv-term Γ tmₓ tm
      then (match-error m-err.e-match-failure) else
    match-ok Xs'

match-types Γ Xs Ls unf tpₓ'@(TpAbs bₓ xₓ tkₓ tpₓ) tp'@(TpAbs b x tk tp) =
  if bₓ xor b
    then (match-types-error m-err.e-match-failure)
    else (match-tpkds Γ Xs Ls (match-unfolding-next unf) tkₓ tk ≫=spans' λ Xs' →  
          match-types (Γ→Γ' Γ) Xs' Ls' (match-unfolding-next unf) tpₓ tp)
  where
  Γ→Γ' : ctxt → ctxt
  Γ→Γ' Γ = ctxt-rename xₓ x (ctxt-var-decl-if x Γ)
  Ls' = stringset-insert Ls x

match-types Γ Xs Ls unf (TpIota xₓ mₓ tpₓ) (TpIota x m tp) =
  match-types Γ Xs Ls (match-unfolding-next unf) mₓ m
  ≫=spans' λ Xs →
    match-types (Γ→Γ' Γ) Xs Ls' (match-unfolding-next unf) tpₓ tp
  where
  Γ→Γ' : ctxt → ctxt
  Γ→Γ' Γ = ctxt-rename xₓ x (ctxt-var-decl-if x Γ)
  Ls' = stringset-insert Ls x

match-types Γ Xs Ls unf (TpEq t₁ₓ t₂ₓ) (TpEq t₁ t₂) =
  if ~ conv-term Γ t₁ₓ t₁
    then match-types-error $ m-err.e-match-failure else
  if ~ conv-term Γ t₂ₓ t₂
    then match-types-error $ m-err.e-match-failure else
  match-types-ok Xs

match-types Γ Xs Ls unf (TpLam xₓ atkₓ tpₓ) (TpLam x atk tp) =
  match-tpkds Γ Xs Ls (match-unfolding-next unf) atkₓ atk ≫=spans' λ Xs →
  match-types (Γ→Γ' Γ) Xs Ls' (match-unfolding-next unf) tpₓ tp
  where
  Γ→Γ' : ctxt → ctxt
  Γ→Γ' Γ = ctxt-rename xₓ x (ctxt-var-decl-if x Γ)
  Ls' = stringset-insert Ls x

match-types Γ Xs Ls unf tpₓ tp =
  match-types-error m-err.e-match-failure

-- match-kinds
-- --------------------------------------------------

-- match-kinds-norm: match already normalized kinds
match-kinds-norm : ctxt → meta-vars → local-vars → match-unfolding-state → (kₓ k : kind) → spanM $ match-error-t meta-vars

-- kind pi
match-kinds-norm Γ Xs Ls uf (KdAbs xₓ tkₓ kₓ) (KdAbs x tk k) =
  match-tpkds Γ Xs Ls uf tkₓ tk ≫=spans' λ Xs →
  match-kinds (Γ→Γ' Γ) Xs Ls' uf kₓ k
  where
  Γ→Γ' = ctxt-rename xₓ x ∘ ctxt-var-decl-if x
  Ls' = stringset-insert Ls x

match-kinds-norm Γ Xs Ls uf KdStar KdStar =
  match-types-ok $ Xs
match-kinds-norm Γ Xs Ls uf kₓ k =
  match-types-error $ m-err.e-matchk-failure -- m-err.e-kind-ineq Γ kₓ k

match-kinds Γ Xs Ls uf kₓ k =
  match-kinds-norm Γ Xs Ls uf
    (hnf Γ unfold-head-elab kₓ)
    (hnf Γ unfold-head-elab k)

-- match-tk
-- --------------------------------------------------
match-tpkds Γ Xs Ls uf (Tkk kₓ) (Tkk k) = match-kinds Γ Xs Ls uf kₓ k
match-tpkds Γ Xs Ls uf (Tkt tpₓ) (Tkt tp) = match-types Γ Xs Ls uf tpₓ tp
match-tpkds Γ Xs Ls uf tkₓ tk =
  match-types-error m-err.e-matchk-failure -- m-err.e-tk-ineq Γ tkₓ tk


-- match-prototype
-- --------------------------------------------------

match-prototype-err : type → prototype → spanM match-prototype-data
match-prototype-err tp pt = spanMr $ mk-match-prototype-data meta-vars-empty (decor-error tp pt) tt

{-
  --------------------
  Xs ⊢? T ≔ ⁇ ⇒ (∅ , T)
-}
match-prototype Γ Xs uf tp (proto-maybe nothing) =
  spanMr $ mk-match-prototype-data Xs (decor-type tp) ff

{-
  Xs ⊢= T ≔ S ⇒ σ
  --------------------
  Xs ⊢? T ≔ S ⇒ (σ , T)
-}
match-prototype Γ Xs uf tp pt@(proto-maybe (just tp')) =
  match-types Γ Xs empty-trie match-unfolding-both tp tp'
    on-fail (λ _ → spanMr $ mk-match-prototype-data Xs (decor-error tp pt) tt)
  ≫=spans' λ Xs' → spanMr $ mk-match-prototype-data Xs' (decor-type tp) ff

{-
  Xs,X ⊢? T ≔ ⁇ → P ⇒ (σ , W)
  -----------------------------------------------
  Xs ⊢? ∀ X . T ≔ ⁇ → P ⇒ (σ - X , ∀ X = σ(X) . W)
-}
match-prototype Γ Xs uf (TpAbs bₓ x (Tkk k) tp) pt'@(proto-arrow e? pt) =
  -- 1) generate a fresh meta-var Y, add it to the meta-vars, and rename
  --    occurences of x in tp to Y
  let ret = meta-vars-add-from-tpabs Γ missing-span-location Xs Erased x k tp
      Y = fst ret ; Xs' = snd ret ; tp' = subst Γ (meta-var-to-type-unsafe Y) x tp
  -- 2) match the body against the original prototype to generate a decorated type
  --    and find some solutions
  in match-prototype Γ Xs' ff tp' pt'
  ≫=span λ ret →
  let mk-match-prototype-data Xs' dt err = ret
      Y' = maybe-else' (meta-vars-lookup Xs' (meta-var-name Y)) Y λ Y → Y
  -- 3) replace the meta-vars with the bound type variable
  in subst-decortype Γ (TpVar x) (meta-var-name Y) dt
  -- 4) leave behind the solution for Y as a decoration and drop Y from Xs
  ≫=span λ dt' →
  let sort' = meta-var.sort (meta-var-set-src Y' checking)
      dt″ = decor-decor Erased x (Tkk k) sort' dt' in
  spanMr $ mk-match-prototype-data (meta-vars-remove Xs' Y) dt″ err

{-
  Xs ⊢? T ≔ P ⇒ (σ , P)
  -----------------------------
  Xs ⊢? S → T ≔ ⁇ → P ⇒ (σ , P)
-}
match-prototype Γ Xs uf (TpAbs b x (Tkt dom) cod) (proto-arrow e? pt) =
  match-prototype Γ Xs ff cod pt
  ≫=span λ ret →
  let mk-match-prototype-data Xs dt err = ret
      dt' = decor-decor b x (Tkt dom) (meta-var-tm dom nothing) dt
  in spanMr $ if b xor e?
    then mk-match-prototype-data meta-vars-empty dt' tt
  else mk-match-prototype-data Xs dt' err

{-
  X ∈ Xs
  -----------------------------------
  Xs ⊢? X ≔ ⁇ → P ⇒ (σ , (X , ⁇ → P))
-}
match-prototype Γ Xs tt tp@(TpVar x) pt@(proto-arrow _ _) =
  spanMr $ mk-match-prototype-data Xs (decor-stuck tp pt) ff

-- everything else...
-- Types for which we should keep digging
match-prototype Γ Xs ff tp@(TpVar x) pt@(proto-arrow _ _) =
  match-prototype Γ Xs tt (hnf Γ unfold-head-elab tp) pt
match-prototype Γ Xs ff tp@(TpApp _ _) pt@(proto-arrow _ _) =
  match-prototype Γ Xs tt (hnf Γ unfold-head-elab tp) pt
-- types for which we should suspend disbelief
match-prototype Γ Xs tt tp@(TpApp _ _) pt@(proto-arrow _ _) =
  spanMr $ mk-match-prototype-data Xs (decor-stuck tp pt) ff
-- types which clearly do not match the prototype
match-prototype Γ Xs uf tp@(TpEq _ _) pt@(proto-arrow _ _) =
  match-prototype-err tp pt
match-prototype Γ Xs uf tp@(TpHole _) pt@(proto-arrow _ _) =
  match-prototype-err tp pt
match-prototype Γ Xs uf tp@(TpLam _ _ _) pt@(proto-arrow _ _) =
  match-prototype-err tp pt
match-prototype Γ Xs uf tp@(TpIota _ _ _) pt@(proto-arrow _ _) =
  match-prototype-err tp pt
