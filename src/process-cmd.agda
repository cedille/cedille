import cedille-options

module process-cmd (options : cedille-options.options) where

open import lib
open import general-util

--open import cedille-find
open import cedille-types
open import classify options {IO}
open import constants
open import conversion
open import ctxt
open import spans options {IO}
open import syntax-util
open import toplevel-state options {IO}
-- open import to-string

import cws-types
import cws

sendProgressUpdate : string → IO ⊤
sendProgressUpdate msg = putStr "progress: " >> putStr msg >> putStr "\n"

sendProgressUpdateFile : (filename : string) → (do-check : 𝔹) → IO ⊤
sendProgressUpdateFile filename do-check = sendProgressUpdate ((if do-check then "Checking " else "Skipping ") ^ filename)

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

check-and-add-params : defScope → posinfo → params → spanM (𝕃 (string × restore-def))
check-and-add-params scope pi' (ParamsCons p@(Decl pi1 pi1' x atk pi2) ps') =
  check-tk atk ≫span
  spanM-add (Decl-span param pi1 x atk pi' {- make this span go to the end of the def, so nesting will work
                                              properly for computing the context in the frontend -}) ≫span
  add-tk' ff scope pi1' x atk ≫=span λ mi →
  check-and-add-params scope pi' ps' ≫=span λ ms → spanMr ((x , mi) :: ms)
check-and-add-params _ _ ParamsNil = spanMr []

dont-check-and-add-params : defScope → posinfo → params → spanM (𝕃 (string × restore-def))
dont-check-and-add-params scope pi' (ParamsCons p@(Decl pi1 pi1' x atk pi2) ps') =
  add-tk' ff scope pi1' x atk ≫=span λ mi →
  dont-check-and-add-params scope pi' ps' ≫=span λ ms → spanMr ((x , mi) :: ms)
dont-check-and-add-params _ _ ParamsNil = spanMr []

{-# TERMINATING #-}
process-cmd : process-t cmd
process-cmds : process-t cmds
process-params : process-t (posinfo × params)
process-start : toplevel-state → (filename : string) → start → (need-to-check : 𝔹) → spanM toplevel-state
process-file : toplevel-state → (filename : string) → IO (toplevel-state × mod-info)

process-cmd (mk-toplevel-state ip fns is Γ) (DefTermOrType (DefTerm pi x (Type tp) t) pi') tt {- check -} = 
  set-ctxt Γ ≫span
  check-type tp (just star) ≫span
  let tp' = qualif-type Γ tp in
  check-term t (just tp') ≫span 
  get-ctxt (λ Γ →
    let Γ' = ctxt-term-def pi globalScope x t tp' Γ in
      spanM-add (DefTerm-span Γ pi x checking (just tp) t pi' []) ≫span
      check-redefined pi x (mk-toplevel-state ip fns is Γ)
        (spanM-add (Var-span Γ' pi x checking (compileFail-in Γ t)) ≫span
         spanMr (mk-toplevel-state ip fns is Γ')))

process-cmd (mk-toplevel-state ip fns is Γ) (DefTermOrType (DefTerm pi x (Type tp) t) pi') ff {- skip checking -} =
  let tp' = qualif-type Γ tp in
    check-redefined pi x (mk-toplevel-state ip fns is Γ)
      (spanMr (mk-toplevel-state ip fns is (ctxt-term-def pi globalScope x t tp' Γ)))

process-cmd (mk-toplevel-state ip fns is Γ) (DefTermOrType (DefTerm pi x NoCheckType t) pi') _ = 
  set-ctxt Γ ≫span
  check-term t nothing ≫=span λ mtp → 
  get-ctxt (λ Γ → 
      let Γ' = maybe-else
                 (ctxt-term-udef pi globalScope x t Γ)
                 (λ tp → ctxt-term-def pi globalScope x t tp Γ) mtp in
      spanM-add (DefTerm-span Γ pi x synthesizing mtp t pi' []) ≫span
      check-redefined pi x (mk-toplevel-state ip fns is Γ)
        (spanM-add (Var-span Γ' pi x synthesizing (compileFail-in Γ t)) ≫span
         spanMr (mk-toplevel-state ip fns is Γ')))

process-cmd (mk-toplevel-state ip fns is Γ) (DefTermOrType (DefType pi x k tp) pi') tt {- check -} =
    set-ctxt Γ ≫span
    check-kind k ≫span 
    let k' = qualif-kind Γ k in
    check-type tp (just k') ≫span 
    get-ctxt (λ Γ → 
      let Γ' = ctxt-type-def pi globalScope x tp k' Γ in
        spanM-add (DefType-span Γ pi x checking (just k) tp pi' []) ≫span
        check-redefined pi x (mk-toplevel-state ip fns is Γ)
          (spanM-add (TpVar-span Γ' pi x checking []) ≫span
           spanMr (mk-toplevel-state ip fns is Γ')))

process-cmd (mk-toplevel-state ip fns is Γ) (DefTermOrType (DefType pi x k tp) pi') ff {- skip checking -} = 
  let k' = qualif-kind Γ k in
    check-redefined pi x (mk-toplevel-state ip fns is Γ)
      (spanMr (mk-toplevel-state ip fns is (ctxt-type-def pi globalScope x tp k' Γ)))

process-cmd (mk-toplevel-state ip fns is Γ) (DefKind pi x ps k pi') tt {- check -} =
  set-ctxt Γ ≫span
  check-and-add-params localScope pi' ps ≫=span λ ms → 
  check-kind k ≫span
  get-ctxt (λ Γ → 
    let Γ' = ctxt-kind-def pi x ps k Γ in
      spanM-add (DefKind-span Γ pi x k pi') ≫span
      check-redefined pi x (mk-toplevel-state ip fns is Γ)
       (spanM-add (KndVar-span Γ' pi x (ArgsNil (posinfo-plus-str pi x)) checking []) ≫span
        spanMr (mk-toplevel-state ip fns is (ctxt-restore-info* Γ' ms))))


process-cmd (mk-toplevel-state ip fns is Γ) (DefKind pi x ps k pi') ff {- skip checking -} = 
  set-ctxt Γ ≫span
  dont-check-and-add-params localScope pi' ps ≫=span λ ms → 
  get-ctxt (λ Γ → 
    let Γ' = ctxt-kind-def pi x ps k Γ in
      check-redefined pi x (mk-toplevel-state ip fns is Γ)
        (spanMr (mk-toplevel-state ip fns is (ctxt-restore-info* Γ' ms))))

-- TODO check import args against module param types
process-cmd s (ImportCmd (Import pi x oa as pi')) _ = 
  let cur-file = ctxt-get-current-filename (toplevel-state.Γ s) in
  let ie = get-include-elt s cur-file in
  case trie-lookup (include-elt.import-to-dep ie) x of λ where
    nothing → spanM-add (Import-span pi "missing" pi' [ error-data "File not found" ])
      ≫span spanMr (set-include-elt s cur-file (record ie {err = tt}))
    (just imported-file) →
      let as = qualif-args (toplevel-state.Γ s) as in
      λ Γ ss → process-file s imported-file >>= λ where
        (s , mod) →
          (let s = scope-imports s imported-file oa as in
           let ie = get-include-elt s imported-file in
             spanM-add (Import-span pi imported-file pi' 
               (if (include-elt.err ie)
                   then [ error-data "There is an error in the imported file" ]
                   else [])) ≫span spanMr s) Γ ss

-- the call to ctxt-update-symbol-occurrences is for cedille-find functionality
process-cmds (mk-toplevel-state include-path files is Γ) (CmdsNext c cs) need-to-check =
  process-cmd (mk-toplevel-state include-path files is Γ) c need-to-check ≫=span λ s →
  process-cmds s cs need-to-check
process-cmds s CmdsStart need-to-check = set-ctxt (toplevel-state.Γ s) ≫span spanMr s

-- TODO ignore checking but still qualify if need-to-check false?
process-params s (pi , ps) need-to-check =
  set-ctxt (toplevel-state.Γ s) ≫span
  check-and-add-params globalScope pi ps ≫=span λ _ →
  spanM-set-params ps ≫span
  get-ctxt λ Γ → 
  spanMr (record s {Γ = Γ})

process-start s filename (File pi is mn ps cs pi') need-to-check =
  λ Γ ss → sendProgressUpdateFile filename need-to-check >>
  (process-cmds s (imps-to-cmds is) need-to-check ≫=span λ s →
   process-params s (pi , ps) need-to-check ≫=span λ s →
   process-cmds s cs need-to-check ≫=span λ s → 
   process-cwst s filename ≫=span λ s →
     spanM-add (File-span pi (posinfo-plus pi' 1) filename) ≫span 
     spanMr s) Γ ss

{- process (type-check if necessary) the given file.  
   We assume the given top-level state has a syntax tree associated with the file. -}
process-file s filename with get-include-elt s filename
process-file s filename | ie =
  proceed s (include-elt.ast ie) (set-need-to-add-symbols-to-context-include-elt ie ff) >>= λ where
    (s , ie , mod) → return (set-include-elt s filename ie , mod)
        {- update the include-elt and the toplevel state (but we will push the updated include-elt into the toplevel state
           just above, after proceed finishes. -}
  where proceed : toplevel-state → maybe start → include-elt → IO (toplevel-state × include-elt × mod-info)
        proceed s nothing ie' = return (s , ie' , (ctxt-get-current-mod (toplevel-state.Γ s))) {- should not happen -}
        proceed s (just x) ie' with include-elt.need-to-add-symbols-to-context ie {- this indeed should be ie, not ie' -}
        proceed (mk-toplevel-state ip fns is Γ) (just x) ie' | tt
          with include-elt.do-type-check ie | ctxt-get-current-mod Γ 
        proceed (mk-toplevel-state ip fns is Γ) (just x) ie' | tt | do-check | prev-mod =
         let Γ = ctxt-initiate-file Γ filename (start-modname x) in
           process-start (mk-toplevel-state ip fns (trie-insert is filename ie') Γ)
                   filename x do-check Γ empty-spans >>= cont
           where cont : toplevel-state × ctxt × spans → IO (toplevel-state × include-elt × mod-info)
                 cont (mk-toplevel-state ip fns is Γ , (mk-ctxt ret-mod _ _ _) , ss) =
                   sendProgressUpdateFile filename do-check >>
                   return (mk-toplevel-state ip (if do-check then (filename :: fns) else fns) is (ctxt-set-current-mod Γ prev-mod) ,
                     (if do-check then set-spans-include-elt ie' ss else ie') ,
                     ret-mod)
        proceed s (just x) ie' | _ = return (s , ie' , (ctxt-get-current-mod (toplevel-state.Γ s)))

