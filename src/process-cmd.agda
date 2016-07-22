module process-cmd where

open import lib

open import cedille-types
open import classify
open import ctxt
open import constants
open import conversion
open import rec
open import spans
open import syntax-util
open import to-string
open import toplevel-state

process-t : Set → Set
process-t X = toplevel-state → X → (need-to-check : 𝔹) → spanM toplevel-state

{-# NO_TERMINATION_CHECK #-}
process-cmd : process-t cmd
process-cmds : process-t cmds
process-start : toplevel-state → (unit-name : string) → start → (need-to-check : 𝔹) → spanM toplevel-state
process-unit : toplevel-state → (unit-name : string) → toplevel-state

process-cmd (mk-toplevel-state ip mod is Γ) (DefTerm pi x (Type tp) t n pi') tt {- check -} = 
  check-type Γ tp (just star) ≫span 
  check-term Γ t (just tp) ≫span 
    let t = erase-term t in
        spanM-add (DefTerm-span pi x checking (just tp) t pi' (normalized-term-if Γ n t)) ≫span 
        spanMr (mk-toplevel-state ip mod is (ctxt-term-def pi x (hnf Γ unfold-head t) tp Γ))

process-cmd (mk-toplevel-state ip mod is Γ) (DefTerm pi x (Type tp) t n pi') ff {- skip checking -} = 
    spanMr (mk-toplevel-state ip mod is (ctxt-term-def pi x (hnf Γ unfold-head t) tp Γ))

process-cmd (mk-toplevel-state ip mod is Γ) (DefTerm pi x NoCheckType t n pi') _ = 
  check-term Γ t nothing ≫=span λ mtp → 
    let t = erase-term t in
      spanM-add (DefTerm-span pi x synthesizing mtp t pi' (normalized-term-if Γ n t)) ≫span
      spanMr (mk-toplevel-state ip mod is (h (hnf Γ unfold-head t , mtp)))
  where h : term × (maybe type) → ctxt
        h (t , nothing) = ctxt-term-udef pi x t Γ
        h (t , just tp) = ctxt-term-def pi x t tp Γ

process-cmd (mk-toplevel-state ip mod is Γ) (DefType pi x (Kind k) tp n pi') tt {- check -} = 
  check-kind Γ k ≫span 
  check-type Γ tp (just k) ≫span 
     spanM-add (DefType-span pi x checking (just k) tp pi' (normalized-type-if Γ n tp)) ≫span 
     spanMr (mk-toplevel-state ip mod is (ctxt-type-def pi x (hnf Γ unfold-head tp) k Γ))

process-cmd (mk-toplevel-state ip mod is Γ) (DefType pi x (Kind k) tp n pi') ff {- skip checking -} = 
  spanMr (mk-toplevel-state ip mod is (ctxt-type-def pi x (hnf Γ unfold-head tp) k Γ))

process-cmd (mk-toplevel-state ip mod is Γ) (CheckTerm t (Type tp) n pi) tt {- check -} = 
  check-type Γ tp (just star) ≫span 
  check-term Γ t (just tp) ≫span 
    let t = erase-term t in
       spanM-add (CheckTerm-span checking (just tp) t pi (normalized-term-if Γ n t)) ≫span 
       spanMr (mk-toplevel-state ip mod is Γ)

process-cmd s (CheckTerm t _ n pi) ff {- skip checking -} = spanMr s

process-cmd (mk-toplevel-state ip mod is Γ) (CheckTerm t NoCheckType n pi) tt {- check -} = 
  check-term Γ t nothing ≫=span λ m → 
     spanM-add (CheckTerm-span synthesizing m t pi (normalized-term-if Γ n t)) ≫span 
     spanMr (mk-toplevel-state ip mod is Γ)

process-cmd s (CheckType tp m n pi) _ = spanMr s -- unimplemented

process-cmd (mk-toplevel-state ip mod is Γ) (DefKind pi x _ k pi') tt {- check -} = 
  check-kind Γ k ≫span
      spanM-add (DefKind-span pi x k pi') ≫span
      spanMr (mk-toplevel-state ip mod is (ctxt-kind-def pi x (hnf Γ unfold-head k) Γ))

process-cmd (mk-toplevel-state ip mod is Γ) (DefKind pi x _ k pi') ff {- skip checking -} = 
  spanMr (mk-toplevel-state ip mod is (ctxt-kind-def pi x (hnf Γ unfold-head k) Γ))

process-cmd s (CheckKind k _ pi) _ = spanMr s -- unimplemented

process-cmd s (Import pi x pi') _ = 
  let s = process-unit s x in
  let ie = get-include-elt s x in
    spanM-add (Import-span pi (include-elt.path ie) pi' 
                (if (include-elt.err ie) then [ error-data "There is an error in the imported file" ] else [])) ≫span
    spanMr s
      

process-cmd (mk-toplevel-state ip mod is Γ) (Rec pi pi'' name params inds ctors body us pi') need-to-check = 
    process-rec-cmd (~ need-to-check) Γ pi pi'' name params inds ctors body us pi' ≫=span λ Γ → 
    spanMr (mk-toplevel-state ip mod is Γ)

process-cmds s (CmdsNext c cs) need-to-check = process-cmd s c need-to-check ≫=span λ s → process-cmds s cs need-to-check
process-cmds s (CmdsStart c) need-to-check = process-cmd s c need-to-check 

process-start s unit-name (File pi cs pi') need-to-check = 
  process-cmds s cs need-to-check ≫=span λ s → 
    spanM-add (File-span pi (posinfo-plus pi' 1) (get-path-for-unit s unit-name)) ≫span 
    spanMr s

process-unit s unit-name with get-include-elt s unit-name
process-unit s unit-name | ie = 
  let p = proceed s (include-elt.ast ie) (set-need-to-add-symbols-to-context-include-elt ie ff) in
    set-include-elt (fst p) unit-name (snd p)
        {- update the include-elt and the toplevel state (but we will push the updated include-elt into the toplevel state
           just above, after proceed finishes. -}
  where proceed : toplevel-state → maybe start → include-elt → toplevel-state × include-elt 
        proceed s nothing ie' = s , ie' {- should not happen -}
        proceed s (just x) ie' with include-elt.need-to-add-symbols-to-context ie {- this indeed should be ie, not ie' -}
        proceed s (just x) ie' | ff = s , ie'
        proceed (mk-toplevel-state ip mod is Γ) (just x) ie' | tt with include-elt.do-type-check ie 
                                                                     | ctxt-get-current-filename Γ | ctxt-get-current-unit-name Γ 
        proceed (mk-toplevel-state ip mod is Γ) (just x) ie' | tt | do-check | prev-path | prev-unit-name =
         let Γ = ctxt-initiate-unit Γ unit-name (include-elt.path (get-include-elt s unit-name)) in
           cont (process-start (mk-toplevel-state ip mod (trie-insert is unit-name ie') Γ)
                   unit-name x do-check (regular-spans []))
           where cont : toplevel-state × spans → toplevel-state × include-elt
                 cont (mk-toplevel-state ip mod is Γ , ss) = 
                   let Γ = ctxt-set-current-unit Γ prev-unit-name prev-path in
                    if do-check then
                      (mk-toplevel-state ip (unit-name :: mod) is Γ , set-spans-include-elt ie' ss)
                    else
                      (mk-toplevel-state ip mod is Γ , ie')


