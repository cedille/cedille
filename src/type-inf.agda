module type-inf where

open import lib
open import functions
open import general-util

open import cedille-types
open import conversion
open import ctxt
open import is-free
open import rename
open import spans
open import subst
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
module _ where
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
solve-var  = string × kind × list type
solve-vars = trie solve-var

solve-var-name : solve-var → var
solve-var-name (x , _ , _) = x

solve-vars-empty : solve-vars
solve-vars-empty = empty-trie

solve-vars-empty? : solve-vars → 𝔹
solve-vars-empty? Xs = ~ (trie-nonempty Xs)

solve-vars-get-sub : solve-vars → trie type
solve-vars-get-sub = trie-map λ where
  (x , k , tps) → case tps of λ where
    (tp :: []) → tp
    _          → TpVar "" x

solve-vars-subst-type : ctxt → solve-vars → type → type
solve-vars-subst-type Γ Xs tp
  = hnf Γ unfold-head-rec-defs
      (substh-type Γ empty-renamectxt (solve-vars-get-sub Xs) tp)
      tt

solve-vars-subst-kind : ctxt → solve-vars → kind → kind
solve-vars-subst-kind Γ Xs k
  = hnf Γ unfold-head-rec-defs
      (substh-kind Γ empty-renamectxt (solve-vars-get-sub Xs) k)
      tt

-- string and span helpers
----------------------------------------
solve-var-to-string : solve-var → strM
solve-var-to-string (x , k , [])
  = strVar x ≫str strAdd " : " ≫str to-stringh k
solve-var-to-string (x , k , sol₁ :: [])
  = strVar x ≫str strAdd " : " ≫str to-stringh k
    ≫str strAdd " = " ≫str to-stringh sol₁
solve-var-to-string (x , k , sol₁ :: sols)
  = strVar x ≫str strAdd " : " ≫str to-stringh k
    ≫str strAdd " = " ≫str to-stringh sol₁ ≫str strAdd "..."

solve-vars-to-stringh : 𝕃 solve-var → strM
solve-vars-to-stringh []
  = strEmpty
solve-vars-to-stringh (v :: [])
  = solve-var-to-string v
solve-vars-to-stringh (v :: vs)
  = solve-var-to-string v ≫str strAdd ", " ≫str solve-vars-to-stringh vs

solve-vars-to-string : solve-vars → strM
solve-vars-to-string Xs = solve-vars-to-stringh (map snd (trie-mappings Xs))

-- TODO move to spans.agda
solve-vars-data : ctxt → solve-vars → 𝕃 tagged-val
solve-vars-data Γ Xs
  = if ~ (trie-nonempty Xs)
    then []
    else [ strRunTag "solve vars" Γ (solve-vars-to-string Xs) ]

solve-vars-check-type-mismatch : ctxt → string → type → solve-vars → type
                                 → 𝕃 tagged-val
solve-vars-check-type-mismatch Γ s tp Xs tp'
  = let tp'' = solve-vars-subst-type Γ Xs tp'
    in  (expected-type Γ tp :: [ type-data Γ tp' ])
        ++ solve-vars-data Γ Xs
        ++ (if conv-type Γ tp tp''
           then []
           else [ error-data
                  ("The expected type does not match the "
                  ^ s ^ "type.") ])

solve-vars-check-type-mismatch-if : maybe type → ctxt → string → solve-vars
                                    → type → 𝕃 tagged-val
solve-vars-check-type-mismatch-if (just tp) Γ s Xs tp'
  = solve-vars-check-type-mismatch Γ s tp Xs tp'
solve-vars-check-type-mismatch-if nothing Γ s Xs tp'
  = type-data Γ tp' :: solve-vars-data Γ Xs
----------------------------------------
----------------------------------------

-- collecting, merging, matching
----------------------------------------------------------------------

-- generate a fresh solve-var
solve-vars-fresh : solve-vars → var → kind → 𝕃 type → solve-var
solve-vars-fresh Xs x k tps
  = rename-away-from ("?" ^ x) (trie-contains Xs) empty-renamectxt
    , k , tps

-- add a solve-var
solve-vars-add : solve-vars → solve-var → solve-vars
solve-vars-add Xs (x , tk@(k , tps)) = trie-insert Xs x (x , tk)

-- unfold a type with solve vars
-- if it's need for a type application
data solve-vars-unfold-tpapp-ret : Set where
  tp-is-kind-abs : posinfo → binder → posinfo → bvar → kind → type → solve-vars-unfold-tpapp-ret

solve-vars-unfold-tpapp : ctxt → solve-vars → type
                          → type ⊎ solve-vars-unfold-tpapp-ret
solve-vars-unfold-tpapp Γ Xs (Abs pi b pi' x (Tkk k) tp)
  = inj₂ (tp-is-kind-abs pi b pi' x k tp)
solve-vars-unfold-tpapp Γ Xs tp
  with solve-vars-subst-type Γ Xs tp
... | Abs pi b pi' x (Tkk k) tp'
    = inj₂ (tp-is-kind-abs pi b pi' x k tp')
... | tp'
    = inj₁ tp'

data solve-vars-unfold-tmapp-ret : Set where
  tp-is-arrow : type → arrowtype → type → solve-vars-unfold-tmapp-ret
  tp-is-tmabs : posinfo → binder → posinfo → bvar → type → type → solve-vars-unfold-tmapp-ret

solve-vars-unfold-tmapp : ctxt → solve-vars → type
                          → type ⊎ solve-vars-unfold-tmapp-ret
solve-vars-unfold-tmapp Γ Xs (Abs pi b pi' x (Tkt tp') tp)
  = inj₂ (tp-is-tmabs pi b pi' x tp' tp)
solve-vars-unfold-tmapp Γ Xs (TpArrow tp₁ at tp₂)
  = inj₂ (tp-is-arrow tp₁ at tp₂)
solve-vars-unfold-tmapp Γ Xs tp
  with solve-vars-subst-type Γ Xs tp
... | (Abs pi b pi' x (Tkt tpₛ') tpₛ)
  = inj₂ (tp-is-tmabs pi b pi' x tpₛ' tpₛ)
... | TpArrow tp₁ at tp₂
  = inj₂ (tp-is-arrow tp₁ at tp₂)
... | tpₛ
  = inj₁ tpₛ

-- peel away one solve-var
-- assumes type is hnf
-- solve-vars-peel : type → solve-vars × type
-- solve-vars-peel (Abs pi b pi' x (Tkk k) tp)
--   -- a solve-var of kind k with no solution
--   = (solve-vars-add {!!} {!!}) , tp -- (snd (solve-vars-add solve-vars-empty (x , k , []))) , tp
-- -- solve-vars-peel (TpParens pi tp pi') = solve-vars-peel tp
-- solve-vars-peel tp = empty-trie , tp

-- -- Collect the leading abstractions of a type, return empty solve-vars (no solution)
-- -- and the body of the abstraction
-- collect-solve-vars : type → solve-vars × type
-- collect-solve-vars (Abs pib b pib' x (Tkk k) tp)
--   with collect-solve-vars tp
-- ... | svs , tp' = trie-insert svs x (k , []) , tp'
-- collect-solve-vars (TpParens pi tp pi')
--   = collect-solve-vars tp
-- -- collect-solve-vars (NoSpans tp x) = {!!}
-- collect-solve-vars tp = empty-trie , tp

-- Merge to sets of solutions
-- merge-solve-vars : ctxt → (X X' : solve-vars) → solve-vars
-- merge-solve-vars Γ X X' = {!!}
