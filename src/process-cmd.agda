module process-cmd where

open import lib

open import cedille-types
open import classify
open import ctxt
open import constants
open import conversion
open import general-util
open import rec
open import spans
open import syntax-util
open import to-string
open import toplevel-state

import cws-types
import cws

-- generate spans from the given comments-and-whitespace syntax tree 
process-cwst-etys : cws-types.entities → spanM ⊤
process-cwst-ety : cws-types.entity → spanM ⊤
process-cwst-etys (cws-types.Entity ety etys) = (process-cwst-ety ety) ≫span process-cwst-etys etys
process-cwst-etys (cws-types.EndEntity ety) = process-cwst-ety ety
process-cwst-ety cws-types.EntityNonws = spanMr triv
process-cwst-ety (cws-types.EntityWs pi pi') = spanMr triv -- spanM-add (whitespace-span pi pi') 
process-cwst-ety (cws-types.EntityComment pi pi') = spanM-add (comment-span pi pi')

process-cwst : toplevel-state → (filename : string) → spanM toplevel-state
process-cwst s filename with include-elt.cwst (get-include-elt s filename)
process-cwst s filename | nothing = spanMr s
process-cwst s filename | just (cws-types.File etys) = process-cwst-etys etys ≫span spanMr s

process-t : Set → Set
process-t X = toplevel-state → X → (need-to-check : 𝔹) → spanM toplevel-state

{-# NO_TERMINATION_CHECK #-}
process-cmd : process-t cmd
process-cmds : process-t cmds
process-start : toplevel-state → (filename : string) → start → (need-to-check : 𝔹) → spanM toplevel-state
process-file : toplevel-state → (filename : string) → toplevel-state

process-cmd (mk-toplevel-state use-cede ip mod is Γ) (DefTerm pi x (Type tp) t n pi') tt {- check -} = 
  set-ctxt Γ ≫span
  check-type tp (just star) ≫span 
  set-ctxt Γ ≫span
  check-term t (just tp) ≫span 
    let t = erase-term t in
    let Γ' = (ctxt-term-def pi x (hnf Γ unfold-head t) tp Γ) in
        spanM-add (DefTerm-span pi x checking (just tp) t pi' (normalized-term-if Γ n t)) ≫span
        spanM-add (Var-span Γ' pi x checking []) ≫span
        spanMr (mk-toplevel-state use-cede ip mod is Γ')

process-cmd (mk-toplevel-state use-cede ip mod is Γ) (DefTerm pi x (Type tp) t n pi') ff {- skip checking -} = 
    spanMr (mk-toplevel-state use-cede ip mod is (ctxt-term-def pi x (hnf Γ unfold-head t) tp Γ))

process-cmd (mk-toplevel-state use-cede ip mod is Γ) (DefTerm pi x NoCheckType t n pi') _ = 
  set-ctxt Γ ≫span
  check-term t nothing ≫=span λ mtp → 
    let t = erase-term t in
      spanM-add (DefTerm-span pi x synthesizing mtp t pi' (normalized-term-if Γ n t)) ≫span
      spanMr (mk-toplevel-state use-cede ip mod is (h (hnf Γ unfold-head t , mtp)))
  where h : term × (maybe type) → ctxt
        h (t , nothing) = ctxt-term-udef pi x t Γ
        h (t , just tp) = ctxt-term-def pi x t tp Γ

process-cmd (mk-toplevel-state use-cede ip mod is Γ) (DefType pi x (Kind k) tp n pi') tt {- check -} =
  let Γ' = (ctxt-type-def pi x (hnf Γ unfold-head tp) k Γ) in
    set-ctxt Γ ≫span
    check-kind k ≫span 
    set-ctxt Γ ≫span
    check-type tp (just k) ≫span 
    spanM-add (DefType-span pi x checking (just k) tp pi' (normalized-type-if Γ n tp)) ≫span
    spanM-add (TpVar-span Γ' pi x checking []) ≫span
    spanMr (mk-toplevel-state use-cede ip mod is Γ')

process-cmd (mk-toplevel-state use-cede ip mod is Γ) (DefType pi x (Kind k) tp n pi') ff {- skip checking -} = 
  spanMr (mk-toplevel-state use-cede ip mod is (ctxt-type-def pi x (hnf Γ unfold-head tp) k Γ))

process-cmd (mk-toplevel-state use-cede ip mod is Γ) (CheckTerm t (Type tp) n pi) tt {- check -} = 
  set-ctxt Γ ≫span
  check-type tp (just star) ≫span 
  set-ctxt Γ ≫span
  check-term t (just tp) ≫span 
    let t = erase-term t in
       spanM-add (CheckTerm-span checking (just tp) t pi (normalized-term-if Γ n t)) ≫span 
       spanMr (mk-toplevel-state use-cede ip mod is Γ)

process-cmd s (CheckTerm t _ n pi) ff {- skip checking -} = spanMr s

process-cmd (mk-toplevel-state use-cede ip mod is Γ) (CheckTerm t NoCheckType n pi) tt {- check -} = 
  set-ctxt Γ ≫span
  check-term t nothing ≫=span λ m → 
     spanM-add (CheckTerm-span synthesizing m t pi (normalized-term-if Γ n t)) ≫span 
     spanMr (mk-toplevel-state use-cede ip mod is Γ)

process-cmd s (CheckType tp m n pi) _ = spanMr s -- unimplemented

process-cmd (mk-toplevel-state use-cede ip mod is Γ) (DefKind pi x _ k pi') tt {- check -} =
  let Γ' = (ctxt-kind-def pi x (hnf Γ unfold-head k) Γ) in
    set-ctxt Γ ≫span
    check-kind k ≫span
        spanM-add (DefKind-span pi x k pi') ≫span
        spanM-add (KndVar-span Γ' pi x checking) ≫span
        spanMr (mk-toplevel-state use-cede ip mod is Γ')

process-cmd (mk-toplevel-state use-cede ip mod is Γ) (DefKind pi x _ k pi') ff {- skip checking -} = 
  spanMr (mk-toplevel-state use-cede ip mod is (ctxt-kind-def pi x (hnf Γ unfold-head k) Γ))

process-cmd s (CheckKind k _ pi) _ = spanMr s -- unimplemented

process-cmd s (Import pi x pi') _ = 
  let cur-file = ctxt-get-current-filename (toplevel-state.Γ s) in
  let ie = get-include-elt s cur-file in
  let imported-file = trie-lookup-string (include-elt.import-to-dep ie) x in
  let s = process-file s imported-file in
  let ie = get-include-elt s imported-file in
    spanM-add (Import-span pi imported-file pi' 
                (if (include-elt.err ie) then [ error-data "There is an error in the imported file" ] else [])) ≫span
    spanMr s
      

process-cmd (mk-toplevel-state use-cede ip mod is Γ) (Rec pi pi'' name params inds ctors body us pi') need-to-check = 
    set-ctxt Γ ≫span
    process-rec-cmd (~ need-to-check) pi pi'' name params inds ctors body us pi' ≫span
      get-ctxt (λ Γ → 
         spanMr (mk-toplevel-state use-cede ip mod is Γ))

process-cmds s (CmdsNext c cs) need-to-check = process-cmd s c need-to-check ≫=span λ s → process-cmds s cs need-to-check
process-cmds s (CmdsStart c) need-to-check = process-cmd s c need-to-check 

process-start s filename (File pi cs pi') need-to-check = 
  process-cmds s cs need-to-check ≫=span λ s → 
  process-cwst s filename ≫=span λ s →
    spanM-add (File-span pi (posinfo-plus pi' 1) filename) ≫span 
    spanMr s

{- process (type-check if necessary) the given file.  
   We assume the given top-level state has a syntax tree associated with the file. -}
process-file s filename with get-include-elt s filename
process-file s filename | ie = 
  let p = proceed s (include-elt.ast ie) (set-need-to-add-symbols-to-context-include-elt ie ff) in
    set-include-elt (fst p) filename (snd p)
        {- update the include-elt and the toplevel state (but we will push the updated include-elt into the toplevel state
           just above, after proceed finishes. -}
  where proceed : toplevel-state → maybe start → include-elt → toplevel-state × include-elt 
        proceed s nothing ie' = s , ie' {- should not happen -}
        proceed s (just x) ie' with include-elt.need-to-add-symbols-to-context ie {- this indeed should be ie, not ie' -}
        proceed s (just x) ie' | ff = s , ie'
        proceed (mk-toplevel-state use-cede ip mod is Γ) (just x) ie' | tt with include-elt.do-type-check ie 
                                                                     | ctxt-get-current-filename Γ 
        proceed (mk-toplevel-state use-cede ip mod is Γ) (just x) ie' | tt | do-check | prev-filename =
         let Γ = ctxt-initiate-file Γ filename in
           cont (process-start (mk-toplevel-state use-cede ip mod (trie-insert is filename ie') Γ)
                   filename x do-check Γ (regular-spans []))
           where cont : toplevel-state × ctxt × spans → toplevel-state × include-elt
                 cont (mk-toplevel-state use-cede ip mod is Γ , _ , ss) = 
                   let Γ = ctxt-set-current-file Γ prev-filename in
                    if do-check then
                      (mk-toplevel-state use-cede ip (filename :: mod) is Γ , set-spans-include-elt ie' ss)
                    else
                      (mk-toplevel-state use-cede ip mod is Γ , ie')


