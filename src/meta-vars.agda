import cedille-options
open import general-util
module meta-vars (options : cedille-options.options) {mF : Set → Set} {{_ : monad mF}} where

open import lib
open import functions

open import cedille-types
open import constants
open import conversion
open import ctxt
open import free-vars
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

  -- sum.agda
  is-inj₁ : ∀ {a b} {A : Set a} {B : Set b} → A ∨ B → 𝔹
  is-inj₁ (inj₁ x) = tt
  is-inj₁ (inj₂ y) = ff

open helpers

-- misc
----------------------------------------------------------------------


-- Meta-variables, prototypes, decorated types
-- ==================================================

record meta-var-sol (A : Set) : Set where
  constructor mk-meta-var-sol
  field
    sol : A
    src : checking-mode

data meta-var-sort : Set where
  meta-var-tp : (k  : kind) → (mtp : maybe $ meta-var-sol type) → meta-var-sort
  meta-var-tm : (tp : type) → (mtm : maybe $ meta-var-sol term) → meta-var-sort

record meta-var : Set where
  constructor meta-var-mk
  field
    name : string
    sort  : meta-var-sort
    loc  : span-location
open meta-var

pattern meta-var-mk-tp x k mtp l = meta-var-mk x (meta-var-tp k mtp) l

record meta-vars : Set where
  constructor meta-vars-mk
  field
    order   : 𝕃 var
    varset  : trie meta-var
open meta-vars

data prototype : Set where
  proto-maybe : maybe type → prototype
  proto-arrow : erased? → prototype → prototype

data decortype : Set where
  decor-type  : type → decortype
  decor-arrow : erased? → type → decortype → decortype
  decor-decor : erased? → var → tpkd → meta-var-sort → decortype → decortype
  decor-stuck : type → prototype → decortype
  decor-error : type → prototype → decortype


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

meta-var-sort-eq? : ctxt → (=S =T : meta-var-sort) → 𝔹
meta-var-sort-eq? Γ (meta-var-tp k₁ mtp₁) (meta-var-tp k₂ mtp₂)
  with conv-kind Γ k₁ k₂
... | ff = ff
... | tt =
  maybe-equal? sol-eq mtp₁ mtp₂
  where
    sol-eq : (sol₁ sol₂ : meta-var-sol type) → 𝔹
    sol-eq (mk-meta-var-sol sol₁ src) (mk-meta-var-sol sol₂ src₁) =
      conv-type Γ sol₁ sol₂

meta-var-sort-eq? _ _ _ = ff
-- TODO terms not supported
-- meta-var-sol-eq? (meta-var-tm tp mtm) (meta-var-tm tp₁ mtm₁) = {!!}

meta-var-equal? : ctxt → (X Y : meta-var) → 𝔹
meta-var-equal? Γ (meta-var-mk name₁ sol₁ _) (meta-var-mk name₂ sol₂ _) =
  name₁ =string name₂ && meta-var-sort-eq? Γ sol₁ sol₂

meta-vars-equal? : ctxt → (Xs Ys : meta-vars) → 𝔹
meta-vars-equal? Γ Xs Ys =
  trie-equal? (meta-var-equal? Γ) (meta-vars.varset Xs) (meta-vars.varset Ys)

meta-vars-lookup : meta-vars → var → maybe meta-var
meta-vars-lookup Xs x = trie-lookup (varset Xs) x

meta-vars-lookup-with-kind : meta-vars → var → maybe (meta-var × kind)
meta-vars-lookup-with-kind Xs x
  with meta-vars-lookup Xs x
... | nothing = nothing
... | (just X@(meta-var-mk-tp _ k _ _)) = just $ X , k
... | (just X) = nothing

meta-var-set-src : meta-var → checking-mode → meta-var
meta-var-set-src (meta-var-mk-tp name₁ k (just sol) loc₁) m =
  meta-var-mk-tp name₁ k (just (record sol { src = m })) loc₁
meta-var-set-src (meta-var-mk-tp name₁ k nothing loc₁) m =
  meta-var-mk-tp name₁ k nothing loc₁
meta-var-set-src (meta-var-mk name₁ (meta-var-tm tp (just sol)) loc₁) m =
  meta-var-mk name₁ (meta-var-tm tp (just (record sol { src = m }))) loc₁
meta-var-set-src (meta-var-mk name₁ (meta-var-tm tp nothing) loc₁) m
  = meta-var-mk name₁ (meta-var-tm tp nothing) loc₁

meta-vars-lookup-kind : meta-vars → var → maybe kind
meta-vars-lookup-kind Xs x with meta-vars-lookup Xs x
... | nothing = nothing
... | (just (meta-var-mk-tp _ k _ _)) = just k
... | (just X) = nothing

-- conversion to types, terms, tks
-- --------------------------------------------------

meta-var-sort-to-tk : meta-var-sort → tpkd
meta-var-sort-to-tk (meta-var-tp k mtp) = Tkk k
meta-var-sort-to-tk (meta-var-tm tp mtm) = Tkt tp

meta-var-to-type : meta-var → maybe type
meta-var-to-type (meta-var-mk-tp x k (just tp) _) = just (meta-var-sol.sol tp)
meta-var-to-type (meta-var-mk-tp x k nothing _) = just (TpVar x)
meta-var-to-type (meta-var-mk x (meta-var-tm tp mtm) _) = nothing

meta-var-to-term : meta-var → maybe term
meta-var-to-term (meta-var-mk-tp x k mtp _) = nothing
meta-var-to-term (meta-var-mk x (meta-var-tm tp (just tm)) _) = just (meta-var-sol.sol tm)
meta-var-to-term (meta-var-mk x (meta-var-tm tp nothing) _) = just (Var x)

meta-var-to-type-unsafe : meta-var → type
meta-var-to-type-unsafe X
  with meta-var-to-type X
... | just tp = tp
... | nothing = TpVar (meta-var-name X)

meta-var-to-term-unsafe : meta-var → term
meta-var-to-term-unsafe X
  with meta-var-to-term X
... | just tm = tm
... | nothing = Var (meta-var-name X)

-- if all meta-vars are solved, return their solutions as args
meta-vars-to-args : meta-vars → maybe args
meta-vars-to-args (meta-vars-mk or vs) =
  flip 𝕃maybe-map or λ x → trie-lookup vs x ≫=maybe λ where
    (meta-var-mk name (meta-var-tm tp tm?) loc) →
      tm? ≫=maybe (just ∘' ArgE ∘' Ttm ∘' meta-var-sol.sol)
    (meta-var-mk name (meta-var-tp kd tp?) loc) →
      tp? ≫=maybe (just ∘' ArgE ∘' Ttp ∘' meta-var-sol.sol)

prototype-to-maybe : prototype → maybe type
prototype-to-maybe (proto-maybe mtp) = mtp
prototype-to-maybe (proto-arrow _ _) = nothing

prototype-to-checking : prototype → checking-mode
prototype-to-checking = maybe-to-checking ∘ prototype-to-maybe

decortype-to-type : decortype → type
decortype-to-type (decor-type tp) = tp
decortype-to-type (decor-arrow at tp dt) =
  TpArrow tp at (decortype-to-type dt)
decortype-to-type (decor-decor b x tk sol dt) =
  TpAbs b x tk (decortype-to-type dt)
decortype-to-type (decor-stuck tp pt) = tp
decortype-to-type (decor-error tp pt) = tp

-- hnf for decortype
-- --------------------------------------------------

hnf-decortype : ctxt → unfolding → decortype → (is-head : 𝔹) → decortype
hnf-decortype Γ uf (decor-type tp) ish =
  decor-type (hnf Γ (record uf {unfold-defs = ish}) tp)
hnf-decortype Γ uf (decor-arrow e? tp dt) ish =
  decor-arrow e? (hnf Γ (record uf {unfold-defs = ff}) tp) (hnf-decortype Γ uf dt ff)
hnf-decortype Γ uf (decor-decor e? x tk sol dt) ish =
  decor-decor e? x tk sol (hnf-decortype Γ uf dt ff)
hnf-decortype Γ uf dt@(decor-stuck _ _) ish = dt
hnf-decortype Γ uf (decor-error tp pt) ish =
  decor-error (hnf Γ (record uf {unfold-defs = ff}) tp) pt

-- substitutions
-- --------------------------------------------------

substh-meta-var-sort : substh-ret-t meta-var-sort
substh-meta-var-sort Γ ρ σ (meta-var-tp k mtp) =
  meta-var-tp (substh Γ ρ σ k) ((flip maybe-map) mtp λ sol →
    record sol { sol = substh Γ ρ σ (meta-var-sol.sol sol) })
substh-meta-var-sort Γ ρ σ (meta-var-tm tp mtm) =
  meta-var-tm (substh Γ ρ σ tp) (flip maybe-map mtm λ sol →
    record sol { sol = substh Γ ρ σ (meta-var-sol.sol sol) })

subst-meta-var-sort : subst-ret-t meta-var-sort
subst-meta-var-sort Γ t x (meta-var-tp k mtp) =
  meta-var-tp (subst Γ t x k) $ (flip maybe-map) mtp λ sol →
    record sol { sol = subst Γ t x $ meta-var-sol.sol sol }

subst-meta-var-sort Γ t x (meta-var-tm tp mtm) =
  meta-var-tm (subst Γ t x tp) $ (flip maybe-map) mtm λ where
    (mk-meta-var-sol sol src) → mk-meta-var-sol (subst Γ t x sol) src

meta-vars-get-sub : meta-vars → trie (Σi exprd ⟦_⟧)
meta-vars-get-sub Xs =
  trie-catMaybe (trie-map (maybe-map ,_ ∘ meta-var-to-type) (varset Xs))

meta-vars-subst-type' : (unfold : 𝔹) → ctxt → meta-vars → type → type
meta-vars-subst-type' u Γ Xs tp =
  let tp' = substs Γ (meta-vars-get-sub Xs) tp in
  if u then hnf Γ unfold-head-elab tp' else tp'

meta-vars-subst-type : ctxt → meta-vars → type → type
meta-vars-subst-type = meta-vars-subst-type' tt

meta-vars-subst-kind : ctxt → meta-vars → kind → kind
meta-vars-subst-kind Γ Xs k
  = hnf Γ unfold-head-elab (substh Γ empty-renamectxt (meta-vars-get-sub Xs) k)

-- string and span helpers
-- --------------------------------------------------

meta-var-to-string : meta-var → strM
meta-var-to-string (meta-var-mk-tp name k nothing sl)
  = strMetaVar name sl
    ≫str strAdd " : " ≫str to-stringe k
meta-var-to-string (meta-var-mk-tp name k (just tp) sl)
  = strMetaVar name sl
    ≫str strAdd " : " ≫str to-stringe k
    ≫str strAdd " = " ≫str to-stringe (meta-var-sol.sol tp) -- tp
meta-var-to-string (meta-var-mk name (meta-var-tm tp nothing) sl)
  = strMetaVar name sl
    ≫str strAdd " : " ≫str to-stringe tp
meta-var-to-string (meta-var-mk name (meta-var-tm tp (just tm)) sl)
  = strMetaVar name sl
    ≫str strAdd " : " ≫str to-stringe tp
    ≫str strAdd " = " ≫str to-stringe (meta-var-sol.sol tm) -- tm

meta-vars-to-stringe : 𝕃 meta-var → strM
meta-vars-to-stringe []
  = strEmpty
meta-vars-to-stringe (v :: [])
  = meta-var-to-string v
meta-vars-to-stringe (v :: vs)
  = meta-var-to-string v ≫str strAdd ", " ≫str meta-vars-to-stringe vs

meta-vars-to-string : meta-vars → strM
meta-vars-to-string Xs =
  meta-vars-to-stringe
    ((flip map) (order Xs) λ x →
      case trie-lookup (varset Xs) x of λ where
        nothing  →
          meta-var-mk
            (x ^ "-missing!") (meta-var-tp KdStar nothing)
            missing-span-location
        (just X) → X)

prototype-to-string : prototype → strM
prototype-to-string (proto-maybe nothing) = strAdd "⁇"
prototype-to-string (proto-maybe (just tp)) = to-stringe tp
prototype-to-string (proto-arrow e? pt) =
  strAdd "⁇" ≫str strAdd (arrowtype-to-string e?)
  ≫str prototype-to-string pt

decortype-to-string : decortype → strM
decortype-to-string (decor-type tp) =
  strAdd "[" ≫str to-stringe tp ≫str strAdd "]"
decortype-to-string (decor-arrow e? tp dt) =
  to-stringe tp
  ≫str strAdd (arrowtype-to-string e?)
  ≫str decortype-to-string dt
decortype-to-string (decor-decor e? x tk sol dt) =
  strAdd (binder e? sol) ≫str meta-var-to-string (meta-var-mk x sol missing-span-location)
  ≫str strAdd "<" ≫str tpkd-to-stringe tk ≫str strAdd ">" ≫str strAdd " . " ≫str decortype-to-string dt
  where
  binder : erased? → meta-var-sort → string
  binder Erased sol = "∀ "
  binder Pi (meta-var-tm tp mtm) = "Π "
  -- vv clause below "shouldn't" happen
  binder Pi (meta-var-tp k mtp) = "∀ "

decortype-to-string (decor-stuck tp pt) =
  strAdd "(" ≫str to-stringe tp ≫str strAdd " , " ≫str prototype-to-string pt ≫str strAdd ")"
decortype-to-string (decor-error tp pt) =
  strAdd "([" ≫str (to-stringe tp) ≫str strAdd "] ‼ " ≫str prototype-to-string pt ≫str strAdd ")"

meta-vars-data-h : ctxt → string → kind ∨ (meta-var-sol type) → tagged-val
meta-vars-data-h Γ X (inj₁ k) =
  strRunTag "meta-vars-intro" Γ
    (strAdd (unqual-local X ^ "  ") ≫str to-stringe k)
meta-vars-data-h Γ X (inj₂ sol) =
  strRunTag "meta-vars-sol" Γ $
  strAdd (unqual-local X ^ " ") ≫str
  strAdd (checking-to-string (meta-var-sol.src sol) ^ " ") ≫str
  (to-stringe ∘ meta-var-sol.sol $ sol)

meta-vars-data-all : ctxt → meta-vars → 𝕃 tagged-val
meta-vars-data-all Γ = foldr
  (uncurry λ where
    _ (meta-var-mk X (meta-var-tp kd nothing) loc) xs →
      meta-vars-data-h Γ X (inj₁ kd) :: xs
    _ (meta-var-mk X (meta-var-tp kd (just tp)) loc) xs →
      meta-vars-data-h Γ X (inj₁ kd)
      :: meta-vars-data-h Γ X (inj₂ tp) :: xs
    _ _ xs → xs)
  [] ∘ (trie-mappings ∘ meta-vars.varset)

meta-vars-intro-data : ctxt → meta-vars → 𝕃 tagged-val
meta-vars-intro-data Γ = map (h ∘ snd) ∘ (trie-mappings ∘ meta-vars.varset)
  where
  h : meta-var → tagged-val
  h (meta-var-mk X (meta-var-tp kd mtp) loc) = meta-vars-data-h Γ X (inj₁ kd)
  h (meta-var-mk X (meta-var-tm tp mtm) loc) =
    meta-vars-data-h Γ X
      (inj₂ (mk-meta-var-sol (TpVar "unimplemented") untyped))

meta-vars-sol-data : ctxt → meta-vars → meta-vars → 𝕃 tagged-val
meta-vars-sol-data Γ Xsₒ Xsₙ = foldr (λ X xs → maybe-else xs (_:: xs) (h (snd X)))
  [] (trie-mappings (meta-vars.varset Xsₙ))
  where
  h : meta-var → maybe tagged-val
  h (meta-var-mk X (meta-var-tp kd (just tp)) loc) with trie-lookup (meta-vars.varset Xsₒ) X
  ...| just (meta-var-mk _ (meta-var-tp _ (just _)) _) = nothing
  ...| _ = just (meta-vars-data-h Γ X (inj₂ tp)
    )
  h (meta-var-mk X (meta-var-tp kd nothing) loc) = nothing
  h (meta-var-mk X (meta-var-tm tp mtm) loc) =
    just (meta-vars-data-h Γ X
      (inj₂ (mk-meta-var-sol (TpVar "unimplemented") untyped)))


meta-vars-check-type-mismatch : ctxt → string → type → meta-vars → type
                                 → 𝕃 tagged-val × err-m
meta-vars-check-type-mismatch Γ s tp Xs tp'
  = (expected-type Γ tp :: [ type-data Γ tp'' ]) ,
    (if conv-type Γ tp tp''
        then nothing
        else just ("The expected type does not match the "
               ^ s ^ " type."))
    where tp'' = meta-vars-subst-type' ff Γ Xs tp'

meta-vars-check-type-mismatch-if : maybe type → ctxt → string → meta-vars
                                    → type → 𝕃 tagged-val × err-m
meta-vars-check-type-mismatch-if (just tp) Γ s Xs tp'
  = meta-vars-check-type-mismatch Γ s tp Xs tp'
meta-vars-check-type-mismatch-if nothing Γ s Xs tp'
  = [ type-data Γ tp″ ] , nothing
  where
  tp″ = meta-vars-subst-type' ff Γ Xs tp'

decortype-data : ctxt → decortype → tagged-val
decortype-data Γ dt = strRunTag "head decoration" Γ (decortype-to-string dt)

prototype-data : ctxt → prototype → tagged-val
prototype-data Γ pt = strRunTag "head prototype" Γ (prototype-to-string pt)


-- collecting, merging, matching
-- --------------------------------------------------

meta-var-fresh-t : (S : Set) → Set
meta-var-fresh-t S = meta-vars → var → span-location → S → meta-var

meta-var-fresh : meta-var-fresh-t meta-var-sort
meta-var-fresh Xs x sl sol
  with fresh-h (trie-contains (varset Xs)) (meta-var-pfx-str ^ x)
... | x' = meta-var-mk x' sol sl

meta-var-fresh-tp : meta-var-fresh-t (kind × maybe (meta-var-sol type))
meta-var-fresh-tp Xs x sl (k , msol) =
  meta-var-fresh Xs x sl (meta-var-tp k msol)

meta-var-fresh-tm : meta-var-fresh-t (type × maybe (meta-var-sol term))
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

meta-vars-from-list : 𝕃 meta-var → meta-vars
meta-vars-from-list Xs = meta-vars-add* meta-vars-empty Xs

meta-vars-remove : meta-vars → meta-var → meta-vars
meta-vars-remove (meta-vars-mk or vs) X =
  let x = meta-var-name X
  in meta-vars-mk (remove _=string_ x or) (trie-remove vs x)

meta-vars-in-type : meta-vars → type → meta-vars
meta-vars-in-type Xs tp =
  let xs = free-vars tp in
  meta-vars-filter (stringset-contains xs ∘ name) Xs

meta-vars-unsolved : meta-vars → meta-vars
meta-vars-unsolved = meta-vars-filter λ where
  (meta-var-mk x (meta-var-tp k mtp) _)  → ~ isJust mtp
  (meta-var-mk x (meta-var-tm tp mtm) _) → ~ isJust mtm

meta-vars-are-free-in-type : meta-vars → type → 𝔹
meta-vars-are-free-in-type Xs tp =
  let xs = free-vars tp in
  list-any (stringset-contains xs) (order Xs)


-- Unfolding a type with meta-vars
-- ==================================================

-- ... in order to reveal a term or type application

-- "View" data structures
-- --------------------------------------------------

-- The decorated type is really an arrow
record is-tmabsd : Set where
  constructor mk-tmabsd
  field
    is-tmabsd-dt  : decortype
    is-tmabsd-e?  : erased?
    is-tmabsd-var : var
    is-tmabsd-dom : type
    is-tmabsd-var-in-body : 𝔹
    is-tmabsd-cod : decortype
open is-tmabsd public

is-tmabsd? = decortype ∨ is-tmabsd

pattern yes-tmabsd dt e? x dom occ cod = inj₂ (mk-tmabsd dt e? x dom occ cod)
pattern not-tmabsd tp = inj₁ tp

record is-tpabsd : Set where
  constructor mk-tpabsd
  field
    is-tpabsd-dt   : decortype
    is-tpabsd-e?   : erased?
    is-tpabsd-var  : var
    is-tpabsd-kind : kind
    is-tpabsd-sol  : maybe type
    is-tpabsd-body : decortype
open is-tpabsd public

is-tpabsd? = decortype ∨ is-tpabsd

pattern yes-tpabsd dt e? x k mtp dt' = inj₂ (mk-tpabsd dt e? x k mtp dt')
pattern not-tpabsd dt = inj₁ dt

{-# TERMINATING #-}
num-arrows-in-type : ctxt → type → ℕ
num-arrows-in-type Γ tp = nait Γ (hnf' Γ tp) 0 tt
  where
  hnf' : ctxt → type → type
  hnf' Γ tp = hnf Γ unfold-head-elab tp

  nait : ctxt → type → (acc : ℕ) → 𝔹 → ℕ
  -- definitely another arrow
  nait Γ (TpAbs _ _ (Tkk _) tp) acc uf = nait Γ tp acc ff
  nait Γ (TpAbs _ _ (Tkt _) tp) acc uf = nait Γ tp (1 + acc) ff
  -- definitely not another arrow
  nait Γ (TpIota _ _ _) acc uf = acc
  nait Γ (TpEq _ _) acc uf = acc
  nait Γ (TpHole _) acc uf = acc
  nait Γ (TpLam _ _ _) acc uf = acc
  nait Γ (TpVar x) acc tt = acc
  nait Γ (TpApp tp₁ tp₂) acc tt = acc
  nait Γ tp acc ff = nait Γ (hnf' Γ tp) acc tt

-- Utilities for match-types in classify.agda
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

module meta-vars-match-errors where
  -- boilerplate
  match-error-msg = "Matching failed"

  -- tagged values for error messages
  match-lhs : {ed : exprd} → ctxt → ⟦ ed ⟧ → tagged-val
  match-lhs = to-string-tag "expected lhs"

  match-rhs : {ed : exprd} → ctxt → ⟦ ed ⟧ → tagged-val
  match-rhs = to-string-tag "computed rhs"

  the-meta-var : var → tagged-val
  the-meta-var = strRunTag "the meta-var" empty-ctxt ∘ strAdd

  the-solution : ctxt → type → tagged-val
  the-solution = to-string-tag "the solution"

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

  e-match-failure : match-error-data
  e-match-failure =
    "The expected argument type is not a (first-order) match of the computed type"
    , []

  e-matchk-failure : match-error-data
  e-matchk-failure =
    "The expected argument kind is not a (first-order) match of the computed kind"
    , []

  e-meta-scope : ctxt → (X tp : type) → match-error-data
--  e-meta-scope : ctxt → (x : var) → (tp₁ tp₂ : type) → match-error-data
  e-meta-scope Γ X tp =
    match-error-msg ^ " because the solution contains a bound variable of the computed argument type"
    , to-string-tag "the meta var" Γ X :: [ to-string-tag "the solution" Γ tp ]

  e-bad-sol-kind : ctxt → (X : var) → (sol : type) → match-error-data
  e-bad-sol-kind Γ X sol =
    "The meta-variable was matched to a type whose kind does not match its own"
    , the-meta-var X :: [ the-solution Γ sol ]

open meta-vars-match-errors

-- meta-vars-match auxiliaries
-- --------------------------------------------------

local-vars = stringset

meta-vars-solve-tp : ctxt → meta-vars → var → type → checking-mode → match-error-t meta-vars
meta-vars-solve-tp Γ Xs x tp m with trie-lookup (varset Xs) x
... | nothing
  = match-error $ x ^ " is not a meta-var!" , []
... | just (meta-var-mk _ (meta-var-tm tp' mtm) _)
  = match-error $ x ^ " is a term meta-var!" , []
... | just (meta-var-mk-tp _ k nothing sl)
  = match-ok (meta-vars-set Xs (meta-var-mk-tp x k (just (mk-meta-var-sol tp m)) sl))
... | just (meta-var-mk-tp _ k (just sol) _) =
  let mk-meta-var-sol tp' src = sol in
  err⊎-guard (~ conv-type Γ tp tp') (e-solution-ineq Γ tp tp x)
  ≫⊎ match-ok Xs

-- update the kinds of HO meta-vars with
-- solutions
meta-vars-update-kinds : ctxt → (Xs Xsₖ : meta-vars) → meta-vars
meta-vars-update-kinds Γ Xs Xsₖ =
  record Xs { varset = (flip trie-map) (varset Xs) λ where
    (meta-var-mk-tp x k mtp sl) → meta-var-mk-tp x (meta-vars-subst-kind Γ Xsₖ k) mtp sl
    sol → sol
  }

hnf-elab-if : {ed : exprd} → 𝔹 → ctxt → ⟦ ed ⟧ → 𝔹 → ⟦ ed ⟧
hnf-elab-if b Γ t b' = if b then hnf Γ (record unfold-head-elab {unfold-defs = b'}) t else t

meta-vars-add-from-tpabs : ctxt → span-location → meta-vars → erased? → var → kind → type → meta-var × meta-vars
meta-vars-add-from-tpabs Γ sl Xs e? x k tp =
  let Y   = meta-var-fresh-tp Xs x sl (k , nothing)
      Xs' = meta-vars-add Xs Y
      tp' = subst Γ (meta-var-to-type-unsafe Y) x tp
  in Y , Xs'

{-
-- Legacy for elaboration.agda
-- ==================================================

-- TODO: remove dependency and delete code


{-# TERMINATING #-} -- subst of a meta-var does not increase distance to arrow
meta-vars-peel : ctxt → span-location → meta-vars → type → (𝕃 meta-var) × type
meta-vars-peel Γ sl Xs (Abs pi e? pi' x tk@(Tkk k) tp)
  with meta-vars-add-from-tpabs Γ sl Xs (mk-tpabs e? x k tp)
... | (Y , Xs')
  with subst Γ (meta-var-to-type-unsafe Y) x tp
... | tp' =
  let ret =  meta-vars-peel Γ sl Xs' tp' ; Ys  = fst ret ; rtp = snd ret
  in (Y :: Ys , rtp)
meta-vars-peel Γ sl Xs (NoSpans tp _) =
  meta-vars-peel Γ sl Xs tp
meta-vars-peel Γ sl Xs (TpParens _ tp _) =
  meta-vars-peel Γ sl Xs tp
meta-vars-peel Γ sl Xs tp = [] , tp

meta-vars-unfold-tpapp : ctxt → meta-vars → type → is-tpabs?
meta-vars-unfold-tpapp Γ Xs tp
  with meta-vars-subst-type Γ Xs tp
... | Abs _ b _ x (Tkk k) tp' = yes-tpabs b x k tp'
... | tp'                        = not-tpabs tp'

meta-vars-unfold-tmapp : ctxt → span-location → meta-vars → type → 𝕃 meta-var × is-tmabs?
meta-vars-unfold-tmapp Γ sl Xs tp
  with meta-vars-peel Γ sl Xs (meta-vars-subst-type Γ Xs tp)
... | Ys , Abs _ b _ x (Tkt dom) cod =
  Ys , yes-tmabs b x dom (is-free-in check-erased x cod) cod
... | Ys , TpArrow dom e? cod =
  Ys , yes-tmabs e? "_" dom ff cod
... | Ys , tp' = Ys , not-tmabs tp'

-}
