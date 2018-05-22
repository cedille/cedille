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
kind-is-star : kind → 𝔹
kind-is-star (Star pi) = tt
kind-is-star _ = ff

-- meta-vars:
-- vars associated with kind and (possibly many) type solutions
----------------------------------------------------------------------
data meta-var-sol : Set where
  meta-var-tp : (k : kind) → (mtp : maybe type) → meta-var-sol
  meta-var-tm : (tp : type) → (mtm : maybe term) → meta-var-sol

record meta-var : Set where
  constructor meta-var-mk
  field
    name : string
    sol  : meta-var-sol
open meta-var

pattern meta-var-mk-tp x k mtp = meta-var-mk x (meta-var-tp k mtp)

record meta-vars : Set where
  constructor meta-vars-mk
  field
    order   : 𝕃 var
    varset  : trie meta-var
open meta-vars

meta-var-name : meta-var → var
meta-var-name X = meta-var.name X

-- TODO
meta-var-to-type : meta-var → posinfo → maybe type
meta-var-to-type (meta-var-mk-tp x k (just tp)) pi = just tp
meta-var-to-type (meta-var-mk-tp x k nothing) pi = just (TpVar pi x)
meta-var-to-type (meta-var-mk x (meta-var-tm tp mtm)) pi = nothing

meta-var-to-term : meta-var → posinfo → maybe term
meta-var-to-term (meta-var-mk-tp x k mtp) pi = nothing
meta-var-to-term (meta-var-mk x (meta-var-tm tp (just tm))) pi = just tm
meta-var-to-term (meta-var-mk x (meta-var-tm tp nothing)) pi = just (Var pi x)

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


meta-vars-empty : meta-vars
meta-vars-empty = meta-vars-mk [] empty-trie -- empty-trie

meta-vars-empty? : meta-vars → 𝔹
meta-vars-empty? Xs = ~ (trie-nonempty (varset Xs )) -- ~ (trie-nonempty Xs)

meta-vars-get-sub : meta-vars → trie type
meta-vars-get-sub Xs
  = trie-catMaybe (trie-map ((flip meta-var-to-type) "") (varset Xs))

-- substitutions, is-free-in
meta-vars-subst-type : ctxt → meta-vars → type → type
meta-vars-subst-type Γ Xs tp
  = hnf Γ (unfolding-elab unfold-head-rec-defs)
      (substh-type Γ empty-renamectxt (meta-vars-get-sub Xs) tp)
      tt

meta-vars-subst-kind : ctxt → meta-vars → kind → kind
meta-vars-subst-kind Γ Xs k
  = hnf Γ (unfolding-elab unfold-head-rec-defs)
      (substh-kind Γ empty-renamectxt (meta-vars-get-sub Xs) k)
      tt

meta-vars-get-varlist : meta-vars → 𝕃 var
meta-vars-get-varlist Xs = map (name ∘ snd) (trie-mappings (varset Xs))

meta-vars-in-type : meta-vars → type → meta-vars
meta-vars-in-type Xs tp
  = record Xs
    { varset = varset'
    ; order  = order'
    }
  where
  varset' = trie-filter
              (λ x → are-free-in-type
                       check-erased (trie-single (name x) triv) tp)
              (varset Xs)
  mvars = trie-strings varset'
  order' = filter (λ x → list-any (x =string_) mvars) (order Xs)


meta-vars-are-free-in-type : meta-vars → type → 𝔹
meta-vars-are-free-in-type Xs tp
  = are-free-in-type check-erased (varset Xs) tp

meta-var-is-HO : meta-var → 𝔹
meta-var-is-HO (meta-var-mk name (meta-var-tm tp mtm)) = tt
meta-var-is-HO (meta-var-mk-tp name k mtp) = kind-is-star k

-- string and span helpers
----------------------------------------
meta-var-to-string : meta-var → strM
meta-var-to-string (meta-var-mk-tp name k nothing)
  = strVar name
    ≫str strAdd " : " ≫str to-stringh k
meta-var-to-string (meta-var-mk-tp name k (just tp))
  = strVar name
    ≫str strAdd " : " ≫str to-stringh k
    ≫str strAdd " = " ≫str to-stringh tp
meta-var-to-string (meta-var-mk name (meta-var-tm tp nothing))
  = strVar name
    ≫str strAdd " : " ≫str to-stringh tp
meta-var-to-string (meta-var-mk name (meta-var-tm tp (just tm)))
  = strVar name
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
meta-vars-to-string Xs = meta-vars-to-stringh (map snd (trie-mappings (varset Xs)))

meta-vars-data : ctxt → meta-vars → 𝕃 tagged-val
meta-vars-data Γ Xs
  = if trie-empty? (varset Xs)
    then []
    else [ strRunTag "meta vars" Γ (meta-vars-to-string Xs) ]

meta-vars-check-type-mismatch : ctxt → string → type → meta-vars → type
                                 → 𝕃 tagged-val × err-m
meta-vars-check-type-mismatch Γ s tp Xs tp'
  = (expected-type Γ tp :: [ type-data Γ tp'' ]) ,
    (if conv-type Γ tp tp''
        then nothing
        else just ("The expected type does not match the "
               ^ s ^ " type."))
    where tp'' = meta-vars-subst-type Γ Xs tp'

meta-vars-check-type-mismatch-if : maybe type → ctxt → string → meta-vars
                                    → type → 𝕃 tagged-val × err-m
meta-vars-check-type-mismatch-if (just tp) Γ s Xs tp'
  = meta-vars-check-type-mismatch Γ s tp Xs tp'
meta-vars-check-type-mismatch-if nothing Γ s Xs tp'
  = [ type-data Γ (meta-vars-subst-type Γ Xs tp') ] , nothing
----------------------------------------
----------------------------------------

-- collecting, merging, matching
----------------------------------------------------------------------

meta-vars-fresh : meta-vars → var → meta-var-sol → meta-var
meta-vars-fresh Xs x sol
  with rename-away-from ("?" ^ x) (trie-contains (varset Xs)) empty-renamectxt
... | x' = meta-var-mk x' sol

meta-vars-fresh-tp : meta-vars → var → kind → maybe type → meta-var
meta-vars-fresh-tp Xs x k mtp = meta-vars-fresh Xs x (meta-var-tp k mtp)

meta-vars-fresh-tm : meta-vars → var → type → maybe term → meta-var
meta-vars-fresh-tm Xs x tp mtm = meta-vars-fresh Xs x (meta-var-tm tp mtm)

private
  meta-vars-set : meta-vars → meta-var → meta-vars
  meta-vars-set Xs X = record Xs { varset = trie-insert (varset Xs) (name X) X }

-- add a meta-var
meta-vars-add : meta-vars → meta-var → meta-vars
meta-vars-add Xs X
 = record (meta-vars-set Xs X) { order = (order Xs) ++ [ name X ] }

-- peel all type quantification var from a type, adding it to a set of
-- meta-vars
{-# TERMINATING #-} -- subst of a meta-var does not increase size of type
meta-vars-peel : ctxt → meta-vars → type → meta-vars × type
meta-vars-peel Γ Xs (TpParens pi tp pi')
  = meta-vars-peel Γ Xs tp
  -- we are only peeling type abstractions, not terms
meta-vars-peel Γ Xs (Abs pi b pi' x tk@(Tkk k) tp)
  with meta-vars-fresh-tp Xs x k nothing
... | X
  with meta-vars-add Xs X
    | subst-type Γ (meta-var-to-type-unsafe X pi) x tp
... | Xs' | tp' = meta-vars-peel Γ Xs' tp'
meta-vars-peel Γ Xs tp
  = Xs , tp

-- unfold a type with solve vars
-- if it's needed for a type application

-- TODO consider abs in is-free
data is-tp-abs : Set where
  yes-tp-abs : posinfo → binder → posinfo → bvar → kind → type → is-tp-abs
  no-tp-abs  : type → is-tp-abs

meta-vars-unfold-tpapp : ctxt → meta-vars → type → is-tp-abs
meta-vars-unfold-tpapp Γ Xs tp
  with meta-vars-subst-type Γ Xs tp
... | Abs pi b pi' x (Tkk k) tp'
  = yes-tp-abs pi b pi' x k tp'
... | tp' = no-tp-abs tp'

data is-tp-arrow : Set where
                     -- tp is the original type, tpₐ the domain
  yes-tp-arrow : (tp tpₐ : type) → (e : maybeErased)
                     → (cod : term → type) → is-tp-arrow
  no-tp-arrow : (htp : type) → is-tp-arrow

private
  ba-to-e : binder ⊎ arrowtype → maybeErased
  ba-to-e (inj₁ All) = Erased
  ba-to-e (inj₁ Pi) = NotErased
  ba-to-e (inj₂ ErasedArrow) = Erased
  ba-to-e (inj₂ UnerasedArrow) = NotErased

meta-vars-unfold-tmapp : ctxt → meta-vars → type → meta-vars × is-tp-arrow
meta-vars-unfold-tmapp Γ Xs tp
  -- substitute all known solutions in immediately, and
  -- peel type abstractions
  with meta-vars-peel Γ Xs (meta-vars-subst-type Γ Xs tp)
... | Xs' , tp'@(Abs _ b _ x (Tkt tpₐ) tpᵣ)
  = Xs' , yes-tp-arrow tp (hnf Γ (unfolding-elab unfold-head-rec-defs) tpₐ tt) (ba-to-e (inj₁ b))
            -- substitute term into codomain (dependent function type)
            (λ t → subst-type Γ (qualif-term Γ t) x tpᵣ)
... | Xs' , tp'@(TpArrow tpₐ at tpᵣ)
  = Xs' , yes-tp-arrow tp (hnf Γ (unfolding-elab unfold-head-rec-defs) tpₐ tt) (ba-to-e (inj₂ at)) (λ _ → tpᵣ)
... | Xs' , tp'
  = Xs' , no-tp-arrow tp'

-- update the kinds of HO meta-vars with
-- solutions
meta-vars-update-kinds : ctxt → (Xs Xsₖ : meta-vars) → meta-vars
meta-vars-update-kinds Γ Xs Xsₖ
  = record Xs { varset = trie-map
      (λ { (meta-var-mk-tp x k mtp)
             → meta-var-mk-tp x (meta-vars-subst-kind Γ Xsₖ k) mtp
         ; sol@(meta-var-mk _ _) → sol})
      (varset Xs)}

-- match a type with meta-vars to one without
----------------------------------------------------------------------

private
  module meta-vars-match-errors where

    e-type-ineq : ctxt → (tp₁ tp₂ : type) → string
    e-type-ineq Γ tp₁ tp₂
      = rope-to-string $'
          to-string Γ tp₁ ⊹⊹ [[ " != " ]] ⊹⊹ to-string Γ tp₂
          ⊹⊹ [[ ", in their definition" ]]

    e-term-ineq : ctxt → (tm₁ tm₂ : term) → string
    e-term-ineq Γ tm₁ tm₂ = rope-to-string $' to-string Γ tm₁ ⊹⊹ [[ " != " ]] ⊹⊹ to-string Γ tm₂

    e-kind-ineq : ctxt → (k₁ k₂ : kind) → string
    e-kind-ineq Γ k₁ k₂ = rope-to-string $' to-string Γ k₁ ⊹⊹ [[ " != " ]] ⊹⊹ to-string Γ k₂

    e-tk-ineq : ctxt → (tk₁ tk₂ : tk) → string
    e-tk-ineq Γ tk₁ tk₂ = rope-to-string $' tk-to-string Γ tk₁ ⊹⊹ [[ " != " ]] ⊹⊹ tk-to-string Γ tk₂

    -- TODO
    e-solution-ineq : ctxt → (tp₁ tp₂ : type) → var → string
    e-solution-ineq Γ tp₁ tp₂ X
      = rope-to-string $'
          to-string Γ tp₁ ⊹⊹ [[ " != " ]] ⊹⊹ to-string Γ tp₂
          ⊹⊹ [[ ", but " ^ X ^ " solved to both" ]]

    e-optType-ineq : ctxt → type → 𝔹 → string
    e-optType-ineq Γ tp tt = rope-to-string $' (to-string Γ tp) ⊹⊹ [[ " != NoType" ]]
    e-optType-ineq Γ tp ff = rope-to-string $' [[ "NoType != " ]] ⊹⊹ to-string Γ tp

    e-arrowtype-ineq : ctxt → (tp₁ tp₂ : type) → string
    e-arrowtype-ineq Γ tp₁ tp₂
      = rope-to-string $'
          to-string Γ tp₁ ⊹⊹ [[ " != " ]]
          ⊹⊹ to-string Γ tp₂
          ⊹⊹ [[ ", in their outermost arrow" ]]

    e-binder-ineq : ctxt → (tp₁ tp₂ : type) (b₁ b₂ : binder) → string
    e-binder-ineq Γ tp₁ tp₂ b₁ b₂ = binder-to-string b₁ ^ " != " ^ binder-to-string b₂

    e-liftingType-ineq : ctxt → (l₁ l₂ : liftingType) → string
    e-liftingType-ineq Γ l₁ l₂
      = rope-to-string $' to-string Γ l₁ ⊹⊹ [[ " != " ]] ⊹⊹ to-string Γ l₂

    e-meta-scope : ctxt → (x : var) → type → string
    e-meta-scope Γ x tp = rope-to-string $'
      [[ "Cannot match " ^ x ^ " with " ]] ⊹⊹ to-string Γ tp
      ⊹⊹ [[ ", because some local vars would escape their scope." ]] 

    e-catchall : ctxt → (tp₁ tp₂ : type) → string
    e-catchall Γ tp₁ tp₂ = e-type-ineq Γ tp₁ tp₂ ^ " (catchall case)"

  open meta-vars-match-errors

local-vars = stringset

meta-vars-solve-tp : ctxt → meta-vars → var → type → error-t meta-vars
meta-vars-solve-tp Γ Xs x tp with trie-lookup (varset Xs) x
... | nothing
  = yes-error $' x ^ " is not a meta-var!"
... | just (meta-var-mk _ (meta-var-tm tp' mtm))
  = yes-error $' x ^ " is a term meta-var!"
... | just (meta-var-mk-tp _ k nothing)
  = no-error (meta-vars-set Xs (meta-var-mk-tp x k (just tp)))
... | just (meta-var-mk-tp _ k (just tp'))
  =   err-guard (~ conv-type Γ tp tp') (e-solution-ineq Γ tp tp' x)
    ≫err no-error Xs

meta-vars-match : ctxt → meta-vars → local-vars → (tpₓ tp : type) → error-t meta-vars
meta-vars-match-tk : ctxt → meta-vars → local-vars → (tkₓ tk : tk) → error-t meta-vars
-- meta-vars-match-optType : ctxt → meta-vars → local-vars → (mₓ m : optType) → error-t meta-vars

-- meta-vars-match
meta-vars-match Γ Xs Ls tpₓ@(TpVar pi x) tp
  -- check if x is a meta-var
  = if ~ trie-contains (meta-vars.varset Xs) x
    -- if not, then just make sure tp is the same var
    then   err-guard (~ conv-type Γ tpₓ tp) (e-type-ineq Γ tpₓ tp)
         ≫err no-error Xs
    -- make sure potential solutions don't bring local variables
    -- out of their scope
    else if are-free-in-type check-erased Ls tp
    then yes-error (e-meta-scope Γ x tp)
    else meta-vars-solve-tp Γ Xs x tp

meta-vars-match Γ Xs Ls (TpApp tpₓ₁ tpₓ₂) (TpApp tp₁ tp₂)
  =   meta-vars-match Γ Xs Ls tpₓ₁ tp₁
    ≫=err λ Xs' → meta-vars-match Γ Xs' Ls tpₓ₂ tp₂
    ≫=err λ Xs″ → no-error Xs″

meta-vars-match Γ Xs Ls (TpAppt tpₓ tmₓ) (TpAppt tp tm)
  =   meta-vars-match Γ Xs Ls tpₓ tp
    ≫=err λ Xs' →
      err-guard (~ conv-term Γ tmₓ tm)
                (e-term-ineq Γ tmₓ tm)
    ≫err no-error Xs'

meta-vars-match Γ Xs Ls tpₓ'@(Abs piₓ bₓ piₓ' xₓ tkₓ tpₓ) tp'@(Abs pi b pi' x tk tp)
  =   err-guard (~ eq-binder bₓ b) (e-binder-ineq Γ tpₓ' tp' bₓ b)
    ≫err meta-vars-match-tk Γ Xs Ls tkₓ tk
    ≫=err λ Xs' →
      meta-vars-match
        (ctxt-rename piₓ' xₓ x (ctxt-var-decl-if pi' x Γ))
        Xs' (stringset-insert Ls x) tpₓ tp

meta-vars-match Γ Xs Ls tpₓ@(TpArrow tp₁ₓ atₓ tp₂ₓ) tp@(TpArrow tp₁ at tp₂)
  =   err-guard (~ eq-arrowtype atₓ at)
                (e-arrowtype-ineq Γ tpₓ tp)
    ≫err meta-vars-match Γ Xs Ls tp₁ₓ tp₁
    ≫=err λ Xs → meta-vars-match Γ Xs Ls tp₂ₓ tp₂

meta-vars-match Γ Xs Ls tpₓ@(TpArrow tp₁ₓ atₓ tp₂ₓ) tp@(Abs _ b _ _ (Tkt tp₁) tp₂)
  =   err-guard (~ arrowtype-matches-binder atₓ b)
                (e-arrowtype-ineq Γ tpₓ tp)
    ≫err meta-vars-match Γ Xs Ls tp₁ₓ tp₁
    ≫=err λ Xs → meta-vars-match Γ Xs Ls tp₂ₓ tp₂

meta-vars-match Γ Xs Ls tpₓ@(Abs _ bₓ _ _ (Tkt tp₁ₓ) tp₂ₓ) tp@(TpArrow tp₁ at tp₂)
  =   err-guard (~ arrowtype-matches-binder at bₓ)
                (e-arrowtype-ineq Γ tpₓ tp)
    ≫err meta-vars-match Γ Xs Ls tp₁ₓ tp₁
    ≫=err λ Xs → meta-vars-match Γ Xs Ls tp₂ₓ tp₂

meta-vars-match Γ Xs Ls (Iota _ piₓ xₓ mₓ tpₓ) (Iota _ pi x m tp)
  =   meta-vars-match Γ Xs Ls mₓ m
    ≫=err λ Xs →
      meta-vars-match (ctxt-rename pi xₓ x (ctxt-var-decl-if pi x Γ))
        Xs (stringset-insert Ls x) tpₓ tp

meta-vars-match Γ Xs Ls (TpEq _ t₁ₓ t₂ₓ _) (TpEq _ t₁ t₂ _)
  =   err-guard (~ conv-term Γ t₁ₓ t₁) (e-term-ineq Γ t₁ₓ t₁)
    ≫err err-guard (~ conv-term Γ t₂ₓ t₂) (e-term-ineq Γ t₂ₓ t₂)
    ≫err no-error Xs

meta-vars-match Γ Xs Ls (Lft _ piₓ xₓ tₓ lₓ) (Lft _ pi x t l)
  =   err-guard (~ conv-liftingType Γ lₓ l) (e-liftingType-ineq Γ lₓ l)
    ≫err err-guard
      (~ conv-term (ctxt-rename piₓ xₓ x (ctxt-var-decl-if pi x Γ)) tₓ t)
      (e-term-ineq Γ tₓ t)
    ≫err no-error Xs

meta-vars-match Γ Xs Ls (TpLambda _ piₓ xₓ atkₓ tpₓ) (TpLambda _ pi x atk tp)
  =   meta-vars-match-tk Γ Xs Ls atkₓ atk
    ≫=err λ Xs → meta-vars-match Γ Xs (stringset-insert Ls x) tpₓ tp

meta-vars-match Γ Xs Ls tpₓ tp
  = yes-error (e-catchall Γ tpₓ tp)

-- meta-vars-match-tk
meta-vars-match-tk Γ Xs Ls (Tkk kₓ) (Tkk k)
  =   err-guard (~ conv-kind Γ kₓ k)
                (e-kind-ineq Γ kₓ k)
    ≫err no-error Xs
meta-vars-match-tk Γ Xs Ls (Tkt tpₓ) (Tkt tp)
  = meta-vars-match Γ Xs Ls tpₓ tp
meta-vars-match-tk Γ Xs Ls tkₓ tk
  = yes-error (e-tk-ineq Γ tkₓ tk)

-- meta-vars-match-optType
{-meta-vars-match-optType Γ Xs Ls NoType NoType
  = no-error Xs
meta-vars-match-optType Γ Xs Ls (SomeType tpₓ) (SomeType tp)
  = meta-vars-match Γ Xs Ls tpₓ tp
meta-vars-match-optType Γ Xs Ls NoType (SomeType tp)
  = yes-error $' e-optType-ineq Γ tp ff
meta-vars-match-optType Γ Xs Ls (SomeType tpₓ) NoType
  = yes-error $' e-optType-ineq Γ tpₓ tt
-}
