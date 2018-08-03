import cedille-options
open import general-util
module meta-vars (options : cedille-options.options) {mF : Set → Set} {{_ : monad mF}} where

open import lib
open import functions

open import cedille-types
open import conversion
open import ctxt
open import is-free
open import rename
open import spans options {mF}
open import subst
open import syntax-util
open import to-string options

-- TODO propose adding these to the standard lib
module helpers where
  -- src/spans.agda
  _≫=spane_ : ∀ {A B : Set} → spanM (error-t A) → (A → spanM (error-t B)) → spanM (error-t B)
  (s₁ ≫=spane f) = s₁ ≫=span
    λ { (no-error x) → f x
      ; (yes-error x) → spanMr (yes-error x)}

  -- functions.agda
  infixr 0 _$'_
  _$'_ : ∀ {a b} {A : Set a} {B : Set b}
         → (A → B) → A → B
  f $' x = f x

  -- sum.agda
  is-inj₁ : ∀ {a b} {A : Set a} {B : Set b} → A ∨ B → 𝔹
  is-inj₁ (inj₁ x) = tt
  is-inj₁ (inj₂ y) = ff

open helpers

-- misc
----------------------------------------------------------------------


-- meta-var type
-- vars associated with kind and (possibly many) type solutions
-- ==================================================

data meta-var-sol : Set where
  meta-var-tp : (k : kind) → (mtp : maybe type) → meta-var-sol
  meta-var-tm : (tp : type) → (mtm : maybe term) → meta-var-sol

record meta-var : Set where
  constructor meta-var-mk
  field
    name : string
    sol  : meta-var-sol
    loc  : span-location
open meta-var

pattern meta-var-mk-tp x k mtp l = meta-var-mk x (meta-var-tp k mtp) l

record meta-vars : Set where
  constructor meta-vars-mk
  field
    order   : 𝕃 var
    varset  : trie meta-var
open meta-vars

-- Simple definitions and accessors
-- --------------------------------------------------

meta-var-name : meta-var → var
meta-var-name X = meta-var.name X

meta-vars-get-varlist : meta-vars → 𝕃 var
meta-vars-get-varlist Xs = map (name ∘ snd) (trie-mappings (varset Xs))

meta-var-solved? : meta-var → 𝔹
meta-var-solved? (meta-var-mk n (meta-var-tp k nothing) _) = ff
meta-var-solved? (meta-var-mk n (meta-var-tp k (just _)) _) = tt
meta-var-solved? (meta-var-mk n (meta-var-tm tp nothing) _) = ff
meta-var-solved? (meta-var-mk n (meta-var-tm tp (just _)) _) = tt

meta-vars-empty : meta-vars
meta-vars-empty = meta-vars-mk [] empty-trie

meta-vars-empty? : meta-vars → 𝔹
meta-vars-empty? Xs = ~ (trie-nonempty (varset Xs ))

meta-vars-solved? : meta-vars → 𝔹
meta-vars-solved? Xs = trie-all meta-var-solved? (varset Xs)

meta-vars-filter : (meta-var → 𝔹) → meta-vars → meta-vars
meta-vars-filter f Xs =
  meta-vars-mk or vs
  where
  vs = trie-filter f (varset Xs)
  or = filter (trie-contains vs) (order Xs)

meta-var-sol-eq? : ctxt → (=S =T : meta-var-sol) → 𝔹
meta-var-sol-eq? Γ (meta-var-tp k₁ mtp₁) (meta-var-tp k₂ mtp₂)
  with conv-kind Γ k₁ k₂
... | ff = ff
... | tt = maybe-equal? (conv-type Γ) mtp₁ mtp₂

meta-var-sol-eq? _ _ _ = ff
-- TODO terms not supported
-- meta-var-sol-eq? (meta-var-tm tp mtm) (meta-var-tm tp₁ mtm₁) = {!!}

meta-var-equal? : ctxt → (X Y : meta-var) → 𝔹
meta-var-equal? Γ (meta-var-mk name₁ sol₁ _) (meta-var-mk name₂ sol₂ _) =
  name₁ =string name₂ && meta-var-sol-eq? Γ sol₁ sol₂

meta-vars-equal? : ctxt → (Xs Ys : meta-vars) → 𝔹
meta-vars-equal? Γ Xs Ys =
  trie-equal? (meta-var-equal? Γ) (meta-vars.varset Xs) (meta-vars.varset Ys)

-- conversion to types and terms
-- --------------------------------------------------

-- TODO
meta-var-to-type : meta-var → posinfo → maybe type
meta-var-to-type (meta-var-mk-tp x k (just tp) _) pi = just tp
meta-var-to-type (meta-var-mk-tp x k nothing _) pi = just (TpVar pi x)
meta-var-to-type (meta-var-mk x (meta-var-tm tp mtm) _) pi = nothing

meta-var-to-term : meta-var → posinfo → maybe term
meta-var-to-term (meta-var-mk-tp x k mtp _) pi = nothing
meta-var-to-term (meta-var-mk x (meta-var-tm tp (just tm)) _) pi = just tm
meta-var-to-term (meta-var-mk x (meta-var-tm tp nothing) _) pi = just (Var pi x)

meta-var-to-type-unsafe : meta-var → posinfo → type
meta-var-to-type-unsafe X pi
  with meta-var-to-type X pi
... | just tp = tp
... | nothing = TpVar pi (meta-var-name X)

meta-var-to-term-unsafe : meta-var → posinfo → term
meta-var-to-term-unsafe X pi
  with meta-var-to-term X pi
... | just tm = tm
... | nothing = Var pi (meta-var-name X)

-- substitutions
-- --------------------------------------------------

meta-vars-get-sub : meta-vars → trie type
meta-vars-get-sub Xs =
  trie-catMaybe (trie-map ((flip meta-var-to-type) "") (varset Xs))

meta-vars-subst-type' : (unfold : 𝔹) → ctxt → meta-vars → type → type
meta-vars-subst-type' u Γ Xs tp =
  let tp' = substh-type Γ empty-renamectxt (meta-vars-get-sub Xs) tp in
  if u then hnf Γ (unfolding-elab unfold-head) tp' tt else tp'

meta-vars-subst-type : ctxt → meta-vars → type → type
meta-vars-subst-type = meta-vars-subst-type' tt

meta-vars-subst-kind : ctxt → meta-vars → kind → kind
meta-vars-subst-kind Γ Xs k
  = hnf Γ (unfolding-elab unfold-head)
      (substh-kind Γ empty-renamectxt (meta-vars-get-sub Xs) k)
      tt

meta-vars-in-type : meta-vars → type → meta-vars
meta-vars-in-type Xs tp =
  (flip meta-vars-filter) Xs λ X →
    are-free-in-type check-erased (trie-single (name X) triv) tp

meta-vars-unsolved : meta-vars → meta-vars
meta-vars-unsolved = meta-vars-filter λ where
  (meta-var-mk x (meta-var-tp k mtp) _)  → ~ isJust mtp
  (meta-var-mk x (meta-var-tm tp mtm) _) → ~ isJust mtm


meta-vars-are-free-in-type : meta-vars → type → 𝔹
meta-vars-are-free-in-type Xs tp
  = are-free-in-type check-erased (varset Xs) tp

-- string and span helpers
----------------------------------------
meta-var-to-string : meta-var → strM
meta-var-to-string (meta-var-mk-tp name k nothing sl)
  = strMetaVar name sl
    ≫str strAdd " : " ≫str to-stringh k
meta-var-to-string (meta-var-mk-tp name k (just tp) sl)
  = strMetaVar name sl
    ≫str strAdd " : " ≫str to-stringh k
    ≫str strAdd " = " ≫str to-stringh tp
meta-var-to-string (meta-var-mk name (meta-var-tm tp nothing) sl)
  = strMetaVar name sl
    ≫str strAdd " : " ≫str to-stringh tp
meta-var-to-string (meta-var-mk name (meta-var-tm tp (just tm)) sl)
  = strMetaVar name sl
    ≫str strAdd " : " ≫str to-stringh tp
    ≫str strAdd " = " ≫str to-stringh tm

meta-vars-to-stringh : 𝕃 meta-var → strM
meta-vars-to-stringh []
  = strEmpty
meta-vars-to-stringh (v :: [])
  = meta-var-to-string v
meta-vars-to-stringh (v :: vs)
  = meta-var-to-string v ≫str strAdd ", " ≫str meta-vars-to-stringh vs

meta-vars-to-string : meta-vars → strM
meta-vars-to-string Xs = -- meta-vars-to-stringh (order Xs) Xs
  meta-vars-to-stringh
    ((flip map) (order Xs) λ x →
      case trie-lookup (varset Xs) x of λ where
        nothing  →
          meta-var-mk
            (x ^ "-missing!") (meta-var-tp (Star posinfo-gen) nothing)
            missing-span-location
        (just X) → X)

meta-vars-data-gen : string → ctxt → meta-vars → 𝕃 tagged-val
meta-vars-data-gen s Γ Xs =
  if trie-empty? (varset Xs)
    then []
    else [ strRunTag s Γ (meta-vars-to-string Xs) ]

meta-vars-data = meta-vars-data-gen "meta vars"
meta-vars-new-data = meta-vars-data-gen "new meta vars"

meta-vars-data-h : ctxt → string → tk → tagged-val
meta-vars-data-h Γ X atk =
  strRunTag (if tk-is-type atk then "meta-vars-sol" else "meta-vars-intro") Γ
    (strAdd (X ^ " ") ≫str to-stringh atk)


meta-vars-data-all : ctxt → meta-vars → 𝕃 tagged-val
meta-vars-data-all Γ = foldr
  (uncurry λ where
    _ (meta-var-mk X (meta-var-tp kd nothing) loc) xs →
      meta-vars-data-h Γ X (Tkk kd) :: xs
    _ (meta-var-mk X (meta-var-tp kd (just tp)) loc) xs →
      meta-vars-data-h Γ X (Tkk kd) :: meta-vars-data-h Γ X (Tkt tp) :: xs
    _ _ xs → xs)
  [] ∘ (trie-mappings ∘ meta-vars.varset)

meta-vars-intro-data : ctxt → meta-vars → 𝕃 tagged-val
meta-vars-intro-data Γ = map (h ∘ snd) ∘ (trie-mappings ∘ meta-vars.varset)
  where
  h : meta-var → tagged-val
  h (meta-var-mk X (meta-var-tp kd mtp) loc) = meta-vars-data-h Γ X (Tkk kd)
  h (meta-var-mk X (meta-var-tm tp mtm) loc) =
    meta-vars-data-h Γ X (Tkt (TpVar posinfo-gen "unimplemented"))

meta-vars-sol-data : ctxt → meta-vars → meta-vars → 𝕃 tagged-val
meta-vars-sol-data Γ Xsₒ Xsₙ = foldr (λ X xs → maybe-else xs (_:: xs) (h (snd X)))
  [] (trie-mappings (meta-vars.varset Xsₙ))
  where
  h : meta-var → maybe tagged-val
  h (meta-var-mk X (meta-var-tp kd (just tp)) loc) with trie-lookup (meta-vars.varset Xsₒ) X
  ...| just (meta-var-mk _ (meta-var-tp _ (just _)) _) = nothing
  ...| _ = just (meta-vars-data-h Γ X (Tkt tp))
  h (meta-var-mk X (meta-var-tp kd nothing) loc) = nothing
  h (meta-var-mk X (meta-var-tm tp mtm) loc) =
    just (meta-vars-data-h Γ X (Tkt (TpVar posinfo-gen "unimplemented")))


meta-vars-check-type-mismatch : ctxt → string → type → meta-vars → type
                                 → 𝕃 tagged-val × err-m
meta-vars-check-type-mismatch Γ s tp Xs tp'
  = (expected-type Γ tp :: [ type-data Γ tp'' ]) ,
    (if conv-type Γ tp tp''
        then nothing
        else just ("The expected type does not match the "
               ^ s ^ " type."))
    where tp'' = meta-vars-subst-type' ff Γ Xs tp'
{-
meta-vars-data-locale : tagged-val
meta-vars-data-locale = "meta-var-locale" , [[]] , []

meta-vars-data-locale-if : 𝔹 → 𝕃 tagged-val
meta-vars-data-locale-if tt = [ meta-vars-data-locale ]
meta-vars-data-locale-if ff = []
-}
{-
meta-vars-data-locality-if : ctxt → meta-vars → 𝔹 → 𝕃 tagged-val
meta-vars-data-locality-if Γ Xs locl? =
  if locl?
  then meta-vars-data-gen "meta-var-locale" Γ Xs
  else []
-}

meta-vars-check-type-mismatch-if : maybe type → ctxt → string → meta-vars
                                    → type → 𝕃 tagged-val × err-m
meta-vars-check-type-mismatch-if (just tp) Γ s Xs tp'
  = meta-vars-check-type-mismatch Γ s tp Xs tp'
meta-vars-check-type-mismatch-if nothing Γ s Xs tp'
  = [ type-data Γ tp″ ] , nothing
  where
  tp″ = meta-vars-subst-type' ff Γ Xs tp'
----------------------------------------
----------------------------------------

-- collecting, merging, matching
-- --------------------------------------------------

meta-var-fresh-t : (S : Set) → Set
meta-var-fresh-t S = meta-vars → var → span-location → S → meta-var

meta-var-fresh : meta-var-fresh-t meta-var-sol
meta-var-fresh Xs x sl sol
  with rename-away-from ("?" ^ x) (trie-contains (varset Xs)) empty-renamectxt
... | x' = meta-var-mk x' sol sl

meta-var-fresh-tp : meta-var-fresh-t (kind × maybe type)
meta-var-fresh-tp Xs x sl (k , mtp) = meta-var-fresh Xs x sl (meta-var-tp k mtp)

meta-var-fresh-tm : meta-var-fresh-t (type × maybe term)
meta-var-fresh-tm Xs x sl (tp , mtm) = meta-var-fresh Xs x sl (meta-var-tm tp mtm)

private
  meta-vars-set : meta-vars → meta-var → meta-vars
  meta-vars-set Xs X = record Xs { varset = trie-insert (varset Xs) (name X) X }

-- add a meta-var
meta-vars-add : meta-vars → meta-var → meta-vars
meta-vars-add Xs X
 = record (meta-vars-set Xs X) { order = (order Xs) ++ [ name X ] }

meta-vars-add* : meta-vars → 𝕃 meta-var → meta-vars
meta-vars-add* Xs [] = Xs
meta-vars-add* Xs (Y :: Ys) = meta-vars-add* (meta-vars-add Xs Y) Ys

-- meta-vars-peel:
-- ==================================================
-- generate meta-variables from the type of the head of an application with
-- leading type abstractions

{-# TERMINATING #-} -- subst of a meta-var does not increase distance to arrow
meta-vars-peel : ctxt → span-location → meta-vars → type → (𝕃 meta-var) × type
meta-vars-peel Γ sl Xs (Abs pi _ _ x tk@(Tkk k) tp) =
  let Y   = meta-var-fresh-tp Xs x sl (k , nothing)
      Xs' = meta-vars-add Xs Y
      tp' = subst-type Γ (meta-var-to-type-unsafe Y pi) x tp
      ret = meta-vars-peel Γ sl Xs' tp' ; Ys  = fst ret ; rtp = snd ret
  in (Y :: Ys , rtp)

meta-vars-peel Γ sl Xs (NoSpans tp _) =
  meta-vars-peel Γ sl Xs tp
meta-vars-peel Γ sl Xs (TpParens _ tp _) =
  meta-vars-peel Γ sl Xs tp
meta-vars-peel Γ sl Xs tp = [] , tp


-- meta-vars-unfold:
-- ==================================================
-- Unfold a type with meta-variables in it to reveal a term or type application

-- TODO consider abs in is-free
data tp-abs : Set where
  mk-tp-abs  : posinfo → maybeErased → posinfo → bvar → kind → type → tp-abs

tp-is-abs : Set
tp-is-abs = type ∨ tp-abs

pattern yes-tp-abs pi b pi' x k tp = inj₂ (mk-tp-abs pi b pi' x k tp)
pattern not-tp-abs tp = inj₁ tp

meta-vars-unfold-tpapp : ctxt → meta-vars → type → tp-is-abs
meta-vars-unfold-tpapp Γ Xs tp
  with meta-vars-subst-type Γ Xs tp
... | Abs pi b pi' x (Tkk k) tp'
  = yes-tp-abs pi b pi' x k tp'
... | tp' = not-tp-abs tp'

data arrow* : Set where
  mk-arrow* : 𝕃 meta-var → (tp dom : type) → (e : maybeErased) → (cod : term → type) → arrow*

tp-is-arrow* : Set
tp-is-arrow* = type ∨ arrow*

pattern yes-tp-arrow* Ys tp dom e cod = inj₂ (mk-arrow* Ys tp dom e cod)
pattern not-tp-arrow* tp = inj₁ tp

arrow*-get-e? : arrow* → maybeErased
arrow*-get-e? (mk-arrow* _ _ _ e _ ) = e

arrow*-get-Xs : arrow* → meta-vars
arrow*-get-Xs (mk-arrow* Lx _ _ _ _) = meta-vars-add* meta-vars-empty Lx

meta-vars-unfold-tmapp : ctxt → span-location → meta-vars → type → tp-is-arrow*
meta-vars-unfold-tmapp Γ sl Xs tp = aux
  where
  aux : tp-is-arrow*
  aux with meta-vars-peel Γ sl Xs (meta-vars-subst-type Γ Xs tp)
  ... | Ys , tp'@(Abs _ b _ x (Tkt dom) cod') =
    yes-tp-arrow* Ys tp' ({-hnf-dom-} dom) b
    (λ t → subst-type Γ t x cod') -- move `qualif-term Γ t' to check-term-spine for elaboration
  ... | Ys , tp'@(TpArrow dom e cod') =
    yes-tp-arrow* Ys tp' ({-hnf-dom-} dom) e
      (λ _ → cod')
  ... | Ys , tp' =
    not-tp-arrow* tp'

-- update the kinds of HO meta-vars with
-- solutions
meta-vars-update-kinds : ctxt → (Xs Xsₖ : meta-vars) → meta-vars
meta-vars-update-kinds Γ Xs Xsₖ =
  record Xs { varset = (flip trie-map) (varset Xs) λ where
    (meta-var-mk-tp x k mtp sl) → meta-var-mk-tp x (meta-vars-subst-kind Γ Xsₖ k) mtp sl
    sol → sol
  }

{-# TERMINATING #-}
num-arrows-in-type : ctxt → type → ℕ
num-arrows-in-type Γ tp = nait Γ (hnf' Γ tp) 0 tt
  where
  hnf' : ctxt → type → type
  hnf' Γ tp = hnf Γ (unfolding-elab unfold-head) tp tt

  nait : ctxt → type → (acc : ℕ) → 𝔹 → ℕ
  -- definitely another arrow
  nait Γ (Abs _ _ _ _ (Tkk _) tp) acc uf = nait Γ tp acc ff
  nait Γ (Abs _ _ _ _ (Tkt _) tp) acc uf = nait Γ tp (1 + acc) ff
  nait Γ (TpArrow _ _ tp) acc uf = nait Γ tp (1 + acc) ff
  -- definitely not another arrow
  nait Γ (Iota _ _ _ _ _) acc uf = acc
  nait Γ (Lft _ _ _ _ _) acc uf = acc
  nait Γ (TpEq _ _ _ _) acc uf = acc
  nait Γ (TpHole _) acc uf = acc
  nait Γ (TpLambda _ _ _ _ _) acc uf = acc
  nait Γ (TpVar x₁ x₂) acc tt = acc
  nait Γ (TpApp tp₁ tp₂) acc tt = acc
  nait Γ (TpAppt tp₁ x₁) acc tt = acc
  -- not sure
  nait Γ (NoSpans tp _) acc uf = nait Γ tp acc uf
  nait Γ (TpLet _ (DefTerm _ x _ tm) tp) acc uf =
    nait Γ (subst-type Γ tm x tp) acc uf
  nait Γ (TpLet _ (DefType _ x _ tp-let) tp-in) acc uf =
    nait Γ (subst-type Γ tp-let x tp-in) acc uf
  nait Γ (TpParens _ tp _) acc uf = nait Γ tp acc uf
  nait Γ tp acc ff = nait Γ (hnf' Γ tp) acc tt

-- meta-vars-match
-- ==================================================
--
-- Match a type with meta-variables in it to one without

-- errors
-- --------------------------------------------------

match-error-data = string × 𝕃 tagged-val

match-error-t : ∀ {a} → Set a → Set a
match-error-t A = match-error-data ∨ A

pattern match-error e = inj₁ e
pattern match-ok a = inj₂ a

private
  module meta-vars-match-errors where
    -- boilerplate
    match-error-msg = "Matching failed"

    -- tagged values for error messages
    match-lhs : {ed : exprd} → ctxt → ⟦ ed ⟧ → tagged-val
    match-lhs = to-string-tag "expected lhs"

    match-rhs : {ed : exprd} → ctxt → ⟦ ed ⟧ → tagged-val
    match-rhs = to-string-tag "computed rhs"

    the-meta-var : var → tagged-val
    the-meta-var x = "the meta-var" , [[ x ]] , []

    fst-snd-sol : {ed : exprd} → ctxt → (t₁ t₂ : ⟦ ed ⟧) → 𝕃 tagged-val
    fst-snd-sol Γ t₁ t₂ =
      to-string-tag "first solution" Γ t₁ :: [ to-string-tag "second solution" Γ t₂ ]

    lhs-rhs : {ed : exprd} → ctxt → (t₁ t₂ : ⟦ ed ⟧) → 𝕃 tagged-val
    lhs-rhs Γ t₁ t₂ = match-lhs Γ t₁ :: [ match-rhs Γ t₂ ]

    -- error-data
    e-solution-ineq : ctxt → (tp₁ tp₂ : type) → var → match-error-data
    e-solution-ineq Γ tp₁ tp₂ X =
      match-error-msg ^ " because it produced two incovertible solutions for a meta-variable"
      , the-meta-var X :: fst-snd-sol Γ tp₁ tp₂

    e-type-ineq : ctxt → (tp₁ tp₂ : type) → match-error-data
    e-type-ineq Γ tp₁ tp₂ =
      match-error-msg ^ " because the lhs and rhs are not equal (or because I'm not very clever)"
      , lhs-rhs Γ tp₁ tp₂

    e-meta-scope : ctxt → (x : var) → (tp₁ tp₂ : type) → match-error-data
    e-meta-scope Γ x tp₁ tp₂ =
      match-error-msg ^ " because a locally bound variable would escape its scope in this match"
      , lhs-rhs Γ tp₁ tp₂ -- may be desirable to have an "escapees" tag?

    e-term-ineq : ctxt → (tm₁ tm₂ : term) → match-error-data
    e-term-ineq Γ tm₁ tm₂ =
      match-error-msg ^ " because the lhs and rhs are not convertible terms"
      , lhs-rhs Γ tm₁ tm₂

    e-binder-ineq : ctxt → (tp₁ tp₂ : type) (b₁ b₂ : maybeErased) → match-error-data
    e-binder-ineq Γ tp₁ tp₂ b₁ b₂ =
      match-error-msg ^ " because the outermost binders of the lhs and rhs are not equal"
      , lhs-rhs Γ tp₁ tp₂

    e-arrowtype-ineq : ctxt → (tp₁ tp₂ : type) → match-error-data
    e-arrowtype-ineq Γ tp₁ tp₂ =
      match-error-msg ^ " because the outermost arrows of the lhs and rhs are not equal"
      , lhs-rhs Γ tp₁ tp₂

    e-liftingType-ineq : ctxt → (l₁ l₂ : liftingType) → match-error-data
    e-liftingType-ineq Γ l₁ l₂ =
      match-error-msg ^ " because the lhs and rhs are not convertible (lifted) types"
      , (lhs-rhs Γ l₁ l₂)

    e-kind-ineq : ctxt → (k₁ k₂ : kind) → match-error-data
    e-kind-ineq Γ k₁ k₂ =
      match-error-msg ^ "because the lhs and rhs are not convertible kinds"
      , lhs-rhs Γ k₁ k₂

    e-tk-ineq : ctxt → (tk₁ tk₂ : tk) → match-error-data
    e-tk-ineq Γ tk₁ tk₂ =
      match-error-msg ^ " because one classifer is a type and the other a kind"
      , lhs-rhs Γ tk₁ tk₂

  open meta-vars-match-errors

-- meta-vars-match auxiliaries
-- --------------------------------------------------

local-vars = stringset

meta-vars-solve-tp : ctxt → meta-vars → var → type → match-error-t meta-vars
meta-vars-solve-tp Γ Xs x tp with trie-lookup (varset Xs) x
... | nothing
  = match-error $' x ^ " is not a meta-var!" , []
... | just (meta-var-mk _ (meta-var-tm tp' mtm) _)
  = match-error $' x ^ " is a term meta-var!" , []
... | just (meta-var-mk-tp _ k nothing sl)
  = match-ok (meta-vars-set Xs (meta-var-mk-tp x k (just tp) sl))
... | just (meta-var-mk-tp _ k (just tp') _)
  =   err⊎-guard (~ conv-type Γ tp tp') (e-solution-ineq Γ tp tp' x)
    ≫⊎ match-ok Xs

record match-state : Set where
  constructor mk-match-state
  field
    do-hnf : 𝔹
    retry  : 𝔹

match-state-toplevel : match-state
match-state-toplevel = record { do-hnf = ff ; retry = tt }

hnf-elab-if : {ed : exprd} → 𝔹 → ctxt → ⟦ ed ⟧ → 𝔹 → ⟦ ed ⟧
hnf-elab-if b Γ t b' = if b then hnf Γ (unfolding-elab unfold-head) t b' else t

-- meta-vars-match main definitions
-- --------------------------------------------------

{-# NON_TERMINATING #-}
meta-vars-match : ctxt → meta-vars → local-vars → match-state → (tpₓ tp : type) → match-error-t meta-vars
meta-vars-match-tk : ctxt → meta-vars → local-vars → match-state → (tkₓ tk : tk) → match-error-t meta-vars
-- meta-vars-match-optType : ctxt → meta-vars → local-vars → (mₓ m : optType) → error-t meta-vars

-- meta-vars-match
meta-vars-match Γ Xs Ls (mk-match-state ff tt) tpₓ tp
  -- attempt a first-order approximation for the match as well as an unfolding one.
  with meta-vars-match Γ Xs Ls (mk-match-state ff ff) tpₓ tp
  | meta-vars-match Γ Xs Ls (mk-match-state tt ff)
      (hnf Γ (unfolding-elab unfold-head) tpₓ tt)
      (hnf Γ (unfolding-elab unfold-head) tp tt)
... | (match-error _) | (match-error msg) = match-error msg
  -- the problem is we can't kind check our solutions here, so the first match
  -- might be bogus. I assume the second match will tend to be more accurate,
  -- but less readable
... | (match-ok _) | (match-error msg) = match-error msg
... | (match-error _) | (match-ok Xs') = match-ok Xs'
... | (match-ok Xs₁) | (match-ok Xs₂) =
  if meta-vars-equal? Γ Xs₁ Xs₂ then match-ok Xs₁ else match-ok Xs₂

meta-vars-match Γ Xs Ls state tpₓ@(TpVar pi x) tp
  -- check if x is a meta-var
  = if ~ trie-contains (meta-vars.varset Xs) x
    -- if not, then just make sure tp is the same var
    then   err⊎-guard (~ conv-type Γ tpₓ tp)
            (e-type-ineq Γ tpₓ tp) -- (e-type-ineq Γ tpₓ tp)
         ≫⊎ match-ok Xs
    -- scope-check solutions
    else if are-free-in-type check-erased Ls tp
    then match-error (e-meta-scope Γ x tpₓ tp)
    else meta-vars-solve-tp Γ Xs x tp

meta-vars-match Γ Xs Ls state (TpApp tpₓ₁ tpₓ₂) (TpApp tp₁ tp₂)
  =   meta-vars-match Γ Xs Ls state tpₓ₁ tp₁
    ≫=⊎ λ Xs' → meta-vars-match Γ Xs' Ls state
                  (hnf-elab-if do-unfold Γ tpₓ₂ tt)
                  (hnf-elab-if do-unfold Γ tp₂ tt)
    ≫=⊎ λ Xs″ → match-ok Xs″
    where do-unfold = match-state.do-hnf state

meta-vars-match Γ Xs Ls state (TpAppt tpₓ tmₓ) (TpAppt tp tm)
  =   meta-vars-match Γ Xs Ls state tpₓ tp
    ≫=⊎ λ Xs' →
      err⊎-guard (~ conv-term Γ tmₓ tm)
        (e-term-ineq Γ tmₓ tm)
    ≫⊎ match-ok Xs'

meta-vars-match Γ Xs Ls state tpₓ'@(Abs piₓ bₓ piₓ' xₓ tkₓ tpₓ) tp'@(Abs pi b pi' x tk tp) =
     err⊎-guard (~ eq-maybeErased bₓ b) (e-binder-ineq Γ tpₓ' tp' bₓ b)
   ≫⊎ meta-vars-match-tk Γ Xs Ls state tkₓ tk
   ≫=⊎ λ Xs' →
      meta-vars-match
        (ctxt-rename piₓ' xₓ x (ctxt-var-decl-if pi' x Γ))
        Xs' (stringset-insert Ls x) state tpₓ tp

meta-vars-match Γ Xs Ls state tpₓ@(TpArrow tp₁ₓ atₓ tp₂ₓ) tp@(TpArrow tp₁ at tp₂)
  =   err⊎-guard (~ eq-maybeErased atₓ at)
       (e-arrowtype-ineq Γ tpₓ tp)
    ≫⊎ meta-vars-match Γ Xs Ls state
      (hnf-elab-if do-unfold Γ tp₁ₓ tt)
      (hnf-elab-if do-unfold Γ tp₁ tt)
    ≫=⊎ λ Xs → meta-vars-match Γ Xs Ls state
      (hnf-elab-if do-unfold Γ tp₂ₓ tt)
      (hnf-elab-if do-unfold Γ tp₂ tt)
    where do-unfold = match-state.do-hnf state

meta-vars-match Γ Xs Ls state tpₓ@(TpArrow tp₁ₓ atₓ tp₂ₓ) tp@(Abs _ b _ _ (Tkt tp₁) tp₂)
  =   err⊎-guard (~ eq-maybeErased atₓ b)
       (e-arrowtype-ineq Γ tpₓ tp)
    ≫⊎ meta-vars-match Γ Xs Ls state
      (hnf-elab-if do-unfold Γ tp₁ₓ tt)
      (hnf-elab-if do-unfold Γ tp₁ tt)
    ≫=⊎ λ Xs → meta-vars-match Γ Xs Ls state
      (hnf-elab-if do-unfold Γ tp₂ₓ tt)
      (hnf-elab-if do-unfold Γ tp₂ tt)
    where do-unfold = match-state.do-hnf state

meta-vars-match Γ Xs Ls state tpₓ@(Abs _ bₓ _ _ (Tkt tp₁ₓ) tp₂ₓ) tp@(TpArrow tp₁ at tp₂)
  =   err⊎-guard (~ eq-maybeErased at bₓ)
       (e-arrowtype-ineq Γ tpₓ tp)
    ≫⊎ meta-vars-match Γ Xs Ls state
      (hnf-elab-if do-unfold Γ tp₁ₓ tt)
      (hnf-elab-if do-unfold Γ tp₁ tt)
    ≫=⊎ λ Xs → meta-vars-match Γ Xs Ls state
      (hnf-elab-if do-unfold Γ tp₂ₓ tt)
      (hnf-elab-if do-unfold Γ tp₂ tt)
    where do-unfold = match-state.do-hnf state

meta-vars-match Γ Xs Ls state (Iota _ piₓ xₓ mₓ tpₓ) (Iota _ pi x m tp)
  =   meta-vars-match Γ Xs Ls state
        (hnf-elab-if do-unfold Γ mₓ tt)
        (hnf-elab-if do-unfold Γ m tt)
    ≫=⊎ λ Xs →
      meta-vars-match (ctxt-rename pi xₓ x (ctxt-var-decl-if pi x Γ))
        Xs (stringset-insert Ls x) state
        (hnf-elab-if do-unfold Γ tpₓ tt)
        (hnf-elab-if do-unfold Γ tp tt)
    where do-unfold = match-state.do-hnf state

meta-vars-match Γ Xs Ls state (TpEq _ t₁ₓ t₂ₓ _) (TpEq _ t₁ t₂ _)
  =   err⊎-guard (~ conv-term Γ t₁ₓ t₁)
       (e-term-ineq Γ t₁ₓ t₁)
    ≫⊎ err⊎-guard (~ conv-term Γ t₂ₓ t₂)
       (e-term-ineq Γ t₂ₓ t₂)
    ≫⊎ match-ok Xs

meta-vars-match Γ Xs Ls state (Lft _ piₓ xₓ tₓ lₓ) (Lft _ pi x t l)
  =   err⊎-guard (~ conv-liftingType Γ lₓ l)
       (e-liftingType-ineq Γ lₓ l)
    ≫⊎ err⊎-guard (~ conv-term (ctxt-rename piₓ xₓ x (ctxt-var-decl-if pi x Γ)) tₓ t)
       (e-term-ineq Γ tₓ t)
    ≫⊎ match-ok Xs

meta-vars-match Γ Xs Ls state (TpLambda _ piₓ xₓ atkₓ tpₓ) (TpLambda _ pi x atk tp)
  =   meta-vars-match-tk Γ Xs Ls state atkₓ atk
    ≫=⊎ λ Xs → meta-vars-match Γ Xs (stringset-insert Ls x) state tpₓ tp

meta-vars-match Γ Xs Ls (mk-match-state ff ff) tpₓ tp =
  match-error (e-type-ineq Γ tpₓ tp)
meta-vars-match Γ Xs Ls (mk-match-state tt _) tpₓ tp =
  match-error (e-type-ineq Γ tpₓ tp)

-- meta-vars-match-tk
meta-vars-match-tk Γ Xs Ls state (Tkk kₓ) (Tkk k)
  =   err⊎-guard (~ conv-kind Γ kₓ k)
       (e-kind-ineq Γ kₓ k)
    ≫⊎ match-ok Xs
meta-vars-match-tk Γ Xs Ls state (Tkt tpₓ) (Tkt tp)
  = meta-vars-match Γ Xs Ls state
      (hnf-elab-if do-unfold Γ tpₓ tt)
      (hnf-elab-if do-unfold Γ tp tt)
    where do-unfold = match-state.do-hnf state

meta-vars-match-tk Γ Xs Ls state tkₓ tk
  = match-error (e-tk-ineq Γ tkₓ tk)

-- meta-vars-match-optType
{-meta-vars-match-optType Γ Xs Ls NoType NoType
  = match-ok Xs
meta-vars-match-optType Γ Xs Ls (SomeType tpₓ) (SomeType tp)
  = meta-vars-match Γ Xs Ls tpₓ tp
meta-vars-match-optType Γ Xs Ls NoType (SomeType tp)
  = yes-error $' e-optType-ineq Γ tp ff
meta-vars-match-optType Γ Xs Ls (SomeType tpₓ) NoType
  = yes-error $' e-optType-ineq Γ tpₓ tt
-}
