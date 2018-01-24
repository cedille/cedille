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
-- open import to-string

import cws-types
import cws

-- generate spans from the given comments-and-whitespace syntax tree 
process-cwst-etys : cws-types.entities → spanM ⊤
process-cwst-ety : cws-types.entity → spanM ⊤
process-cwst-etys (cws-types.Entity ety etys) = (process-cwst-ety ety) ≫span process-cwst-etys etys
process-cwst-etys cws-types.EndEntity = spanMr triv
process-cwst-ety cws-types.EntityNonws = spanMr triv
process-cwst-ety (cws-types.EntityWs pi pi') = spanMr triv -- spanM-add (whitespace-span pi pi') 
process-cwst-ety (cws-types.EntityComment pi pi') = spanM-add (comment-span pi pi')

process-cwst : toplevel-state → (filename : string) → spanM toplevel-state
process-cwst s filename with include-elt.cwst (get-include-elt s filename)
process-cwst s filename | nothing = spanMr s
process-cwst s filename | just (cws-types.File etys) = process-cwst-etys etys ≫span spanMr s

process-t : Set → Set
process-t X = toplevel-state → X → (need-to-check : 𝔹) → spanM toplevel-state

check-and-add-params : posinfo → params → spanM (𝕃 (string × maybe sym-info))
check-and-add-params pi' (ParamsCons (Decl pi1 pi1' x atk pi2) ps') =
  check-tk atk ≫span
  spanM-add (Decl-span param pi1 x atk pi' {- make this span go to the end of the def, so nesting will work
                                              properly for computing the context in the frontend -}) ≫span
  add-tk pi1' x atk ≫=span λ mi → 
  check-and-add-params pi' ps' ≫=span λ ms → spanMr ((x , mi) :: ms)
check-and-add-params _ ParamsNil = spanMr []

{-# TERMINATING #-}
process-cmd : process-t cmd
process-cmds : process-t cmds
process-params : process-t (posinfo × params)
process-start : toplevel-state → (filename : string) → start → (need-to-check : 𝔹) → spanM toplevel-state
process-file : toplevel-state → (filename : string) → toplevel-state × mod-info

process-cmd (mk-toplevel-state use-cede make-rkt ip fns is Γ) (DefTermOrType (DefTerm pi x (Type tp) t) pi') tt {- check -} = 
  set-ctxt Γ ≫span
  check-type tp (just star) ≫span
  let tp' = qualif-type Γ tp in
  check-term t (just tp') ≫span 
  get-ctxt (λ Γ → 
    let t = erase-term t in
    let t' = hnf Γ unfold-head t tt in
    let Γ' = ctxt-term-def pi globalScope x t' tp' Γ in
      spanM-add (DefTerm-span Γ pi x checking (just tp) t pi' []) ≫span
      check-redefined pi x (mk-toplevel-state use-cede make-rkt ip fns is Γ)
        (spanM-add (Var-span Γ' pi x checking []) ≫span
         spanMr (mk-toplevel-state use-cede make-rkt ip fns is Γ')))

process-cmd (mk-toplevel-state use-cede make-rkt ip fns is Γ) (DefTermOrType (DefTerm pi x (Type tp) t) pi') ff {- skip checking -} =
  let tp' = qualif-type Γ tp in
  let t' = hnf Γ unfold-head t tt in
    check-redefined pi x (mk-toplevel-state use-cede make-rkt ip fns is Γ)
      (spanMr (mk-toplevel-state use-cede make-rkt ip fns is (ctxt-term-def pi globalScope x t' tp' Γ)))

process-cmd (mk-toplevel-state use-cede make-rkt ip fns is Γ) (DefTermOrType (DefTerm pi x NoCheckType t) pi') _ = 
  set-ctxt Γ ≫span
  check-term t nothing ≫=span λ mtp → 
  get-ctxt (λ Γ → 
    let t = erase-term t in
    let t' = hnf Γ unfold-head t tt in
      spanM-add (DefTerm-span Γ pi x synthesizing mtp t pi' []) ≫span
      check-redefined pi x (mk-toplevel-state use-cede make-rkt ip fns is Γ)
        (spanMr (mk-toplevel-state use-cede make-rkt ip fns is (h Γ (t' , mtp)))))
  where h : ctxt → term × (maybe type) → ctxt
        h Γ (t , nothing) = ctxt-term-udef pi globalScope x t Γ
        h Γ (t , just tp) = ctxt-term-def pi globalScope x t tp Γ

process-cmd (mk-toplevel-state use-cede make-rkt ip fns is Γ) (DefTermOrType (DefType pi x k tp) pi') tt {- check -} =
    set-ctxt Γ ≫span
    check-kind k ≫span 
    let k' = qualif-kind Γ k in
    check-type tp (just k') ≫span 
    get-ctxt (λ Γ → 
      let tp' = hnf Γ unfold-head tp tt in
      let Γ' = ctxt-type-def pi globalScope x tp' k' Γ in
        spanM-add (DefType-span Γ pi x checking (just k) tp pi' []) ≫span
        check-redefined pi x (mk-toplevel-state use-cede make-rkt ip fns is Γ)
          (spanM-add (TpVar-span Γ' pi x checking []) ≫span
           spanMr (mk-toplevel-state use-cede make-rkt ip fns is Γ')))

process-cmd (mk-toplevel-state use-cede make-rkt ip fns is Γ) (DefTermOrType (DefType pi x k tp) pi') ff {- skip checking -} = 
  let k' = qualif-kind Γ k in
  let tp' = hnf Γ unfold-head tp tt in
    check-redefined pi x (mk-toplevel-state use-cede make-rkt ip fns is Γ)
      (spanMr (mk-toplevel-state use-cede make-rkt ip fns is (ctxt-type-def pi globalScope x tp' k' Γ)))

process-cmd (mk-toplevel-state use-cede make-rkt ip fns is Γ) (DefKind pi x ps k pi') tt {- check -} =
  set-ctxt Γ ≫span
  check-and-add-params pi' ps ≫=span λ ms → 
  check-kind k ≫span
  get-ctxt (λ Γ → 
    let k' = hnf Γ unfold-head k tt in
    -- TODO maybe need to qualif params ps
    let Γ' = ctxt-kind-def pi x ps k' Γ in
      spanM-add (DefKind-span Γ pi x k pi') ≫span
      check-redefined pi x (mk-toplevel-state use-cede make-rkt ip fns is Γ)
       (spanM-add (KndVar-span Γ' pi x (ArgsNil (posinfo-plus-str pi x)) checking []) ≫span
        spanMr (mk-toplevel-state use-cede make-rkt ip fns is (ctxt-restore-info* Γ' ms))))
  where check-and-add-params : posinfo → params → spanM (𝕃 (string × restore-def))
        check-and-add-params pi' (ParamsCons (Decl pi1 pi1' x atk pi2) ps') =
          check-tk atk ≫span
          spanM-add (Decl-span param pi1 x atk pi' {- make this span go to the end of the def, so nesting will work
                                                      properly for computing the context in the frontend -}) ≫span
          add-tk pi1' x atk ≫=span λ mi → 
          check-and-add-params pi' ps' ≫=span λ ms → spanMr ((x , mi) :: ms)
        check-and-add-params _ ParamsNil = spanMr []

process-cmd (mk-toplevel-state use-cede make-rkt ip fns is Γ) (DefKind pi x ps k pi') ff {- skip checking -} = 
  let k' = hnf Γ unfold-head k tt in
    check-redefined pi x (mk-toplevel-state use-cede make-rkt ip fns is Γ)
      (spanMr (mk-toplevel-state use-cede make-rkt ip fns is (ctxt-kind-def pi x ps k' Γ)))

-- TODO check import args against module param types
process-cmd s (ImportCmd (Import pi x oa as pi')) _ = 
  let cur-file = ctxt-get-current-filename (toplevel-state.Γ s) in
  let ie = get-include-elt s cur-file in
  let imported-file = trie-lookup-string (include-elt.import-to-dep ie) x in
  let s = scope-imports (fst (process-file s imported-file)) imported-file oa as in
  let ie = get-include-elt s imported-file in
    spanM-add (Import-span pi imported-file pi' 
                (if (include-elt.err ie) then [ error-data "There is an error in the imported file" ] else [])) ≫span
    spanMr s
      

-- the call to ctxt-update-symbol-occurrences is for cedille-find functionality
process-cmds (mk-toplevel-state use-cede make-rkt include-path files is Γ) (CmdsNext c cs) need-to-check = process-cmd
                                (mk-toplevel-state use-cede make-rkt include-path files is
                                  {-(ctxt-set-symbol-occurrences Γ
                                    (find-symbols-cmd c (ctxt-get-current-filename Γ) (ctxt-get-symbol-occurrences Γ) empty-stringset))-} Γ)
                                c need-to-check ≫=span
                                λ s → process-cmds s cs need-to-check
process-cmds s CmdsStart need-to-check = set-ctxt (toplevel-state.Γ s) ≫span spanMr s

-- TODO ignore checking but still qualify if need-to-check false?
process-params s (pi , ps) need-to-check =
  set-ctxt (toplevel-state.Γ s) ≫span
  check-and-add-params pi ps ≫=span λ _ →
  get-ctxt λ Γ → 
  spanMr (record s {Γ = Γ})

process-start s filename (File pi is mn ps cs pi') need-to-check =
  process-cmds s (imps-to-cmds is) need-to-check ≫=span λ s →
  process-params s (pi , ps) need-to-check ≫=span λ s →
  process-cmds s cs need-to-check ≫=span λ s → 
  process-cwst s filename ≫=span λ s →
    spanM-add (File-span pi (posinfo-plus pi' 1) filename) ≫span 
    spanMr s

{- process (type-check if necessary) the given file.  
   We assume the given top-level state has a syntax tree associated with the file. -}
process-file s filename with get-include-elt s filename
process-file s filename | ie = 
  let p = proceed s (include-elt.ast ie) (set-need-to-add-symbols-to-context-include-elt ie ff) in
    set-include-elt (fst p) filename (fst (snd p)) , snd (snd p)
        {- update the include-elt and the toplevel state (but we will push the updated include-elt into the toplevel state
           just above, after proceed finishes. -}
  where proceed : toplevel-state → maybe start → include-elt → toplevel-state × include-elt × mod-info
        proceed s nothing ie' = s , ie' , (ctxt-get-current-mod (toplevel-state.Γ s)) {- should not happen -}
        proceed s (just x) ie' with include-elt.need-to-add-symbols-to-context ie {- this indeed should be ie, not ie' -}
        proceed s (just x) ie' | ff = s , ie' , (ctxt-get-current-mod (toplevel-state.Γ s))
        proceed (mk-toplevel-state use-cede make-rkt ip fns is Γ) (just x) ie' | tt
          with include-elt.do-type-check ie | ctxt-get-current-mod Γ 
        proceed (mk-toplevel-state use-cede make-rkt ip fns is Γ) (just x) ie' | tt | do-check | prev-mod =
         let Γ = ctxt-initiate-file Γ filename (start-modname x) in
           cont (process-start (mk-toplevel-state use-cede make-rkt ip fns (trie-insert is filename ie') Γ)
                   filename x do-check Γ (regular-spans []))
           where cont : toplevel-state × ctxt × spans → toplevel-state × include-elt × mod-info
                 cont (mk-toplevel-state use-cede make-rkt ip fns is Γ , (mk-ctxt ret-mod _ _ _) , ss) = 
                   let Γ = ctxt-set-current-mod Γ prev-mod in
                    if do-check then
                      (mk-toplevel-state use-cede make-rkt ip (filename :: fns) is Γ , set-spans-include-elt ie' ss , ret-mod)
                    else
                      (mk-toplevel-state use-cede make-rkt ip fns is Γ , ie' , ret-mod)

