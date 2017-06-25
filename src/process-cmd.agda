module process-cmd where

open import lib

--open import cedille-find
open import cedille-types
open import classify
open import constants
open import conversion
open import ctxt
open import general-util
open import spans
open import syntax-util
open import toplevel-state
open import to-string

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

{-# TERMINATING #-}
process-cmd : process-t cmd
process-cmds : process-t cmds
process-start : toplevel-state → (filename : string) → start → (need-to-check : 𝔹) → spanM toplevel-state
process-file : toplevel-state → (filename : string) → toplevel-state

process-cmd (mk-toplevel-state use-cede ip mod is Γ) (DefTerm pi x (Type tp) t pi') tt {- check -} = 
  set-ctxt Γ ≫span
  check-type tp (just star) ≫span 
  check-term t (just tp) ≫span 
  get-ctxt (λ Γ → 
    let t = erase-term t in
    let Γ' = (ctxt-term-def pi x (hnf Γ unfold-head t tt) tp Γ) in
      spanM-add (DefTerm-span pi x checking (just tp) t pi' []) ≫span
      check-redefined pi x (mk-toplevel-state use-cede ip mod is Γ)
        (spanM-add (Var-span Γ' pi x checking []) ≫span
         spanMr (mk-toplevel-state use-cede ip mod is Γ')))

process-cmd (mk-toplevel-state use-cede ip mod is Γ) (DefTerm pi x (Type tp) t pi') ff {- skip checking -} = 
    check-redefined pi x (mk-toplevel-state use-cede ip mod is Γ)
      (spanMr (mk-toplevel-state use-cede ip mod is (ctxt-term-def pi x (hnf Γ unfold-head t tt) tp Γ)))

process-cmd (mk-toplevel-state use-cede ip mod is Γ) (DefTerm pi x NoCheckType t pi') _ = 
  set-ctxt Γ ≫span
  check-term t nothing ≫=span λ mtp → 
  get-ctxt (λ Γ → 
    let t = erase-term t in
      spanM-add (DefTerm-span pi x synthesizing mtp t pi' []) ≫span
      check-redefined pi x (mk-toplevel-state use-cede ip mod is Γ)
        (spanMr (mk-toplevel-state use-cede ip mod is (h Γ (hnf Γ unfold-head t tt , mtp)))))
  where h : ctxt → term × (maybe type) → ctxt
        h Γ (t , nothing) = ctxt-term-udef pi x t Γ
        h Γ (t , just tp) = ctxt-term-def pi x t tp Γ

process-cmd (mk-toplevel-state use-cede ip mod is Γ) (DefType pi x (Kind k) tp pi') tt {- check -} =
    set-ctxt Γ ≫span
    check-kind k ≫span 
    check-type tp (just k) ≫span 
    get-ctxt (λ Γ → 
      let Γ' = (ctxt-type-def pi x (hnf Γ unfold-head tp tt) k Γ) in
        spanM-add (DefType-span pi x checking (just k) tp pi' []) ≫span
        check-redefined pi x (mk-toplevel-state use-cede ip mod is Γ)
          (spanM-add (TpVar-span Γ' pi x checking []) ≫span
           spanMr (mk-toplevel-state use-cede ip mod is Γ')))

process-cmd (mk-toplevel-state use-cede ip mod is Γ) (DefType pi x (Kind k) tp pi') ff {- skip checking -} = 
  check-redefined pi x (mk-toplevel-state use-cede ip mod is Γ)
    (spanMr (mk-toplevel-state use-cede ip mod is (ctxt-type-def pi x (hnf Γ unfold-head tp tt) k Γ)))

process-cmd (mk-toplevel-state use-cede ip mod is Γ) (DefKind pi x ps k pi') tt {- check -} =
  set-ctxt Γ ≫span
  check-and-add-params pi' ps ≫=span λ ms → 
  check-kind k ≫span
  get-ctxt (λ Γ → 
    let Γ' = (ctxt-kind-def pi x ps (hnf Γ unfold-head k tt) Γ) in
      spanM-add (DefKind-span pi x k pi') ≫span
      check-redefined pi x (mk-toplevel-state use-cede ip mod is Γ)
       (spanM-add (KndVar-span Γ' pi x (ArgsNil (posinfo-plus-str pi x)) checking []) ≫span
        spanMr (mk-toplevel-state use-cede ip mod is (ctxt-restore-info* Γ' ms))))

  where check-and-add-params : posinfo → params → spanM (𝕃 (string × maybe sym-info))
        check-and-add-params pi' (ParamsCons (Decl pi1 pi1' x atk pi2) ps') =
          check-tk atk ≫span
          spanM-add (Decl-span param pi1 x atk pi' {- make this span go to the end of the def, so nesting will work
                                                      properly for computing the context in the frontend -}) ≫span
          add-tk pi1' x atk ≫=span λ mi → 
          check-and-add-params pi' ps' ≫=span λ ms → spanMr ((x , mi) :: ms)
        check-and-add-params _ ParamsNil = spanMr []

process-cmd (mk-toplevel-state use-cede ip mod is Γ) (DefKind pi x ps k pi') ff {- skip checking -} = 
  check-redefined pi x (mk-toplevel-state use-cede ip mod is Γ)
    (spanMr (mk-toplevel-state use-cede ip mod is (ctxt-kind-def pi x ps (hnf Γ unfold-head k tt) Γ)))

process-cmd s (Import pi x pi') _ = 
  let cur-file = ctxt-get-current-filename (toplevel-state.Γ s) in
  let ie = get-include-elt s cur-file in
  let imported-file = trie-lookup-string (include-elt.import-to-dep ie) x in
  let s = process-file s imported-file in
  let ie = get-include-elt s imported-file in
    spanM-add (Import-span pi imported-file pi' 
                (if (include-elt.err ie) then [ error-data "There is an error in the imported file" ] else [])) ≫span
    spanMr s
      

-- the call to ctxt-update-symbol-occurrences is for cedille-find functionality
process-cmds (mk-toplevel-state use-cede include-path files is Γ) (CmdsNext c cs) need-to-check = process-cmd
                                (mk-toplevel-state use-cede include-path files is
                                  {-(ctxt-set-symbol-occurrences Γ
                                    (find-symbols-cmd c (ctxt-get-current-filename Γ) (ctxt-get-symbol-occurrences Γ) empty-stringset))-} Γ)
                                c need-to-check ≫=span
                                λ s → process-cmds s cs need-to-check
process-cmds s CmdsStart need-to-check = spanMr s

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


