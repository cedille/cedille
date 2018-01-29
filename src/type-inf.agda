module type-inf where

open import lib
open import functions
open import general-util

open import cedille-types
open import conversion
open import ctxt
open import is-free
open import spans
open import syntax-util
open import to-string

-- TODO propose adding these to the standard lib
module helpers where
  -- src/spans.agda
  _≫=spane_ : ∀ {A B : Set} → spanM (error-t A) → (A → spanM (error-t B)) → spanM (error-t B)
  (s₁ ≫=spane f) = s₁ ≫=span
    λ { (no-error x) → f x
      ; (yes-error x) → spanMr (yes-error x)}


open helpers

-- kind restriction on solve vars (System F kinds only)
----------------------------------------------------------------------
data fkind : Set where 
    FKndParens : posinfo → fkind → posinfo → fkind
    FStar : posinfo → fkind

kind-to-fkind : kind → maybe fkind
kind-to-fkind (Star pi) = just (FStar pi)
kind-to-fkind (KndParens pi k pi')
  = kind-to-fkind k ≫=maybe λ fk → just (FKndParens pi fk pi')
kind-to-fkind _ = nothing

fkind-to-kind : fkind → kind
fkind-to-kind (FKndParens pi k pi') = KndParens pi (fkind-to-kind k) pi'
fkind-to-kind (FStar pi) = Star pi

-- Solve vars:
-- vars associated with kind and (possibly many) type solutions
----------------------------------------------------------------------
solve-vars = trie (kind × list type)

-- string and span helpers
solve-vars-to-string : ctxt → solve-vars → string
solve-vars-to-string Γ sv
  = string-concat-sep ","
      ((flip map) (trie-mappings sv)
        λ { (x , k , sols)
            → x ^ " : " ^ to-string Γ k})

-- TODO move to spans.agda
solve-var-set-data : ctxt → solve-vars → tagged-val
solve-var-set-data Γ xs = "solve vars" , solve-vars-to-string Γ xs

-- collecting, merging, matching

-- Collect the leading abstractions of a type, return empty solve-vars (no solution)
-- and the body of the abstraction
collect-solve-vars : type → solve-vars × type
collect-solve-vars (Abs pib b pib' x (Tkk k) tp)
  with collect-solve-vars tp
... | svs , tp' = trie-insert svs x (k , []) , tp'
collect-solve-vars (TpParens pi tp pi')
  = collect-solve-vars tp
-- collect-solve-vars (NoSpans tp x) = {!!}
collect-solve-vars tp = empty-trie , tp

-- Merge to sets of solutions
-- merge-solve-vars : ctxt → (X X' : solve-vars) → solve-vars
-- merge-solve-vars Γ X X' = {!!}
