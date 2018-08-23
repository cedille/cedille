import cedille-options
open import general-util
open import lib

module process-cmd
  (options : cedille-options.options)
  {mF : Set → Set}
  {{_ : monad mF}}
  (progress-update : string → 𝔹 → mF ⊤) where

--open import cedille-find
open import cedille-types
open import classify options {mF}
open import constants
open import conversion
open import ctxt
open import spans options {mF}
open import syntax-util
open import toplevel-state options {mF}
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

process-cwst : toplevel-state → filepath → spanM toplevel-state
process-cwst s filename with include-elt.cwst (get-include-elt s filename)
process-cwst s filename | nothing = spanMr s
process-cwst s filename | just (cws-types.File etys) = process-cwst-etys etys ≫span spanMr s

process-t : Set → Set
process-t X = toplevel-state → X → (need-to-check : 𝔹) → spanM toplevel-state

check-and-add-params : defScope → posinfo → params → spanM (𝕃 (string × restore-def))
check-and-add-params scope pi' (ParamsCons p@(Decl pi1 pi1' me x atk pi2) ps') =
  check-tk atk ≫span
  spanM-add (Decl-span param pi1 x atk pi' {- make this span go to the end of the def, so nesting will work
                                              properly for computing the context in the frontend -}) ≫span
  add-tk' (me-erased me) scope pi1' x atk ≫=span λ mi →
  check-and-add-params scope pi' ps' ≫=span λ ms → spanMr ((x , mi) :: ms)
check-and-add-params _ _ ParamsNil = spanMr []

dont-check-and-add-params : defScope → posinfo → params → spanM (𝕃 (string × restore-def))
dont-check-and-add-params scope pi' (ParamsCons p@(Decl pi1 pi1' me x atk pi2) ps') =
  add-tk' (me-erased me) scope pi1' x atk ≫=span λ mi →
  dont-check-and-add-params scope pi' ps' ≫=span λ ms → spanMr ((x , mi) :: ms)
dont-check-and-add-params _ _ ParamsNil = spanMr []

optAs-posinfo-var : optAs → (posinfo × var) → spanM (posinfo × var)
optAs-posinfo-var NoOptAs = spanMr
optAs-posinfo-var (SomeOptAs pi x) orig = get-ctxt λ Γ →
  spanM-add (Import-module-span Γ orig ParamsNil [ not-for-navigation ] nothing) ≫span spanMr (pi , x)

add-params-kind : params → kind → kind
add-params-kind (ParamsCons (Decl pi pi' m v k'  pi'') ps) k =
  KndPi pi pi' v k' (add-params-kind ps k)
add-params-kind ParamsNil k = k

{-# TERMINATING #-}
process-consts : dataConsts → params → spanM ⊤
process-cmd : process-t cmd
process-cmds : process-t cmds
process-params : process-t (posinfo × params)
process-start : toplevel-state → filepath → (progress-name : string) → start → (need-to-check : 𝔹) → spanM toplevel-state
process-file : toplevel-state → filepath → (progress-name : string) → mF (toplevel-state × mod-info)
 
process-cmd (mk-toplevel-state ip fns is Γ) (DefTermOrType op (DefTerm pi x (SomeType tp) t) pi') tt {- check -} = 
  set-ctxt Γ ≫span
  check-type tp (just star) ≫span
  let tp' = qualif-type Γ tp in
  check-term t (just tp') ≫span 
  check-erased-margs t (just tp') ≫span 
  get-ctxt (λ Γ →
    let Γ' = ctxt-term-def pi globalScope op x t tp' Γ in
      spanM-add (DefTerm-span Γ' pi x checking (just tp) t pi' []) ≫span
      check-redefined pi x (mk-toplevel-state ip fns is Γ)
        (spanM-add (uncurry (Var-span Γ' pi x checking) (compileFail-in Γ t)) ≫span
         spanMr (mk-toplevel-state ip fns is Γ')))

process-cmd (mk-toplevel-state ip fns is Γ) (DefTermOrType op (DefTerm pi x (SomeType tp) t) pi') ff {- skip checking -} =
  let tp' = qualif-type Γ tp in
    check-redefined pi x (mk-toplevel-state ip fns is Γ)
      (spanMr (mk-toplevel-state ip fns is (ctxt-term-def pi globalScope op x t tp' Γ)))


process-cmd (mk-toplevel-state ip fns is Γ) (DefTermOrType op (DefTerm pi x NoType t) pi') _ = 
  set-ctxt Γ ≫span
  check-term t nothing ≫=span λ mtp → 
  check-erased-margs t nothing ≫span 
  get-ctxt (λ Γ → 
      let Γ' = maybe-else
                 (ctxt-term-udef pi globalScope op x t Γ)
                 (λ tp → ctxt-term-def pi globalScope op x t tp Γ) mtp in
      spanM-add (DefTerm-span Γ' pi x synthesizing mtp t pi' []) ≫span
      check-redefined pi x (mk-toplevel-state ip fns is Γ)
        (spanM-add (uncurry (Var-span Γ' pi x synthesizing) (compileFail-in Γ t)) ≫span
         spanMr (mk-toplevel-state ip fns is Γ')))

process-cmd (mk-toplevel-state ip fns is Γ) (DefTermOrType op (DefType pi x k tp) pi') tt {- check -} =
    set-ctxt Γ ≫span
    check-kind k ≫span 
    let k' = qualif-kind Γ k in
    check-type tp (just k') ≫span 
    get-ctxt (λ Γ → 
      let Γ' = ctxt-type-def pi globalScope op x tp k' Γ in
        spanM-add (DefType-span Γ' pi x checking (just k) tp pi' []) ≫span
        check-redefined pi x (mk-toplevel-state ip fns is Γ)
          (spanM-add (TpVar-span Γ' pi x checking [] nothing) ≫span
           spanMr (mk-toplevel-state ip fns is Γ')))


process-cmd (mk-toplevel-state ip fns is Γ) (DefTermOrType op (DefType pi x k tp) pi') ff {- skip checking -} = 
  let k' = qualif-kind Γ k in
    check-redefined pi x (mk-toplevel-state ip fns is Γ)
      (spanMr (mk-toplevel-state ip fns is (ctxt-type-def pi globalScope op x tp k' Γ)))

process-cmd (mk-toplevel-state ip fns is Γ) (DefKind pi x ps k pi') tt {- check -} =
  set-ctxt Γ ≫span
  check-and-add-params localScope pi' ps ≫=span λ ms → 
  check-kind k ≫span
  get-ctxt (λ Γ → 
    let Γ' = ctxt-kind-def pi x ps k Γ in
      spanM-add (DefKind-span Γ' pi x k pi') ≫span
      check-redefined pi x (mk-toplevel-state ip fns is Γ)
       (spanM-add (KndVar-span Γ' (pi , x) (posinfo-plus-str pi x) ps checking [] nothing) ≫span
        spanMr (mk-toplevel-state ip fns is (ctxt-restore-info* Γ' ms))))


process-cmd (mk-toplevel-state ip fns is Γ) (DefKind pi x ps k pi') ff {- skip checking -} = 
  set-ctxt Γ ≫span
  dont-check-and-add-params localScope pi' ps ≫=span λ ms → 
  get-ctxt (λ Γ → 
    let Γ' = ctxt-kind-def pi x ps k Γ in
      check-redefined pi x (mk-toplevel-state ip fns is Γ)
        (spanMr (mk-toplevel-state ip fns is (ctxt-restore-info* Γ' ms))))

-- TODO ignore checking but still gen spans if need-to-check false?
process-cmd s (ImportCmd (Import pi op pi' x oa as pi'')) _ =
  let fnₒ = ctxt-get-current-filename (toplevel-state.Γ s)
      ie = get-include-elt s fnₒ in
  case trie-lookup (include-elt.import-to-dep ie) x of λ where
    nothing → spanM-add (Import-span pi "missing" pi'' [] (just ("File not found: " ^ x)))
      ≫span spanMr (set-include-elt s fnₒ (record ie {err = tt}))
    (just fnᵢ) Γ ss →
      process-file s fnᵢ x ≫=monad uncurry λ s _ →
        (let s-e = scope-file s fnₒ fnᵢ oa (qualif-args (toplevel-state.Γ s) as) in
         process-import op oa fnₒ fnᵢ (lookup-mod-params (toplevel-state.Γ s) fnᵢ) ≫=span λ e →
         spanM-add (Import-span pi fnᵢ pi'' [] (snd s-e maybe-or e)) ≫span spanMr (fst s-e)) Γ ss
  where
  process-import : optPublic → optAs → (cur imp : filepath) → maybe params → spanM err-m
  process-import op oa fnₒ fnᵢ nothing = spanMr (just "Undefined module import (this probably shouldn't happen?)")
  process-import IsPublic (SomeOptAs _ _) fnₒ fnᵢ (just ParamsNil) = spanMr (just "Public import can't be qualified")
  process-import IsPublic oa fnₒ fnᵢ (just (ParamsCons _ _)) = spanMr (just "Public imports cant' have module parameters")
  process-import op oa fnₒ fnᵢ (just ps) =
    optAs-posinfo-var oa (pi' , x) ≫=span λ pi-v →
    with-ctxt (toplevel-state.Γ s)
      (check-args-against-params (just (location-data (fnᵢ , first-position))) pi-v ps as) ≫span
    spanMr nothing
{-
(just imported-file) →
-      λ Γ ss → process-file s imported-file x ≫=monad λ { (s , _) →
-        (let ie = get-include-elt s imported-file in
-         get-ctxt λ Γ →
-         (with-ctxt (toplevel-state.Γ s) (optAs-posinfo-var oa (pi' , x))) ≫=span λ pi-v →
-         maybe-else
-           (spanMr (just ("Undefined module import")))
-           (λ ps → with-ctxt (toplevel-state.Γ s)
-             (check-args-against-params (just (location-data (imported-file , first-position))) pi-v ps as ≫span
-              spanMr nothing))
-           (lookup-mod-params (toplevel-state.Γ s) imported-file) ≫=span λ err →
-           spanM-add (Import-span pi imported-file pi'' []
-           (if (include-elt.err ie)
-               then just "There is an error in the imported file"
-               else err)) ≫span
-         spanMr (scope-file s imported-file oa (qualif-args (toplevel-state.Γ s) as))) Γ ss}

-}

process-cmd (mk-toplevel-state ip fns is Γ) (DefDatatype dd@(Datatype pi pix x ps k cs _) pi') _  =
    set-ctxt Γ ≫span
    check-kind (add-params-kind ps k) ≫span -- 
    get-ctxt (λ Γ → 
      let Γ' = ctxt-datatype-def pi x (qualif-params Γ ps) (qualif-kind Γ (add-params-kind ps k)) (Datatype pi pix x ps k cs pi') Γ in
        set-ctxt Γ'                                          ≫span
        spanM-add (DefDatatype-span pi pix x pi')            ≫span
        spanM-add (TpVar-span Γ' pix x checking [] nothing)  ≫span
        process-consts cs ps                                 ≫span
        get-ctxt (λ Γ →
          spanMr (mk-toplevel-state ip fns is Γ))) --(ctxt-restore-info* Γ ms))))

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
  spanMr (record s {Γ = ctxt-add-current-params Γ})

process-start s filename pn (File pi0 is pi1 pi2 mn ps cs pi3) need-to-check =
  λ Γ ss → progress-update pn need-to-check ≫monad
  (process-cmds s (imps-to-cmds is) need-to-check ≫=span λ s →
   process-params s (pi0 , ps) need-to-check ≫=span λ s →
   process-cmds s cs need-to-check ≫=span λ s → 
   process-cwst s filename ≫=span λ s →
     spanM-add (File-span (toplevel-state.Γ s) pi0 (posinfo-plus pi3 1) filename) ≫span
     let pi2' = posinfo-plus-str pi2 mn in
     spanM-add (Module-span pi2 pi2') ≫span
     spanM-add (Module-header-span pi1 pi2') ≫span
     spanMr s) Γ ss

{- process (type-check if necessary) the given file.  
   We assume the given top-level state has a syntax tree associated with the file. -}
process-file s filename pn with get-include-elt s filename
process-file s filename pn | ie =
  proceed s (include-elt.ast ie) (set-need-to-add-symbols-to-context-include-elt ie ff) ≫=monad λ where
    (s , ie , ret-mod) → returnM (set-include-elt s filename ie , ret-mod)
        {- update the include-elt and the toplevel state (but we will push the updated include-elt into the toplevel state
           just above, after proceed finishes. -}
  where proceed : toplevel-state → maybe start → include-elt → mF (toplevel-state × include-elt × mod-info)
        proceed s nothing ie' = progress-update filename tt ≫monad returnM (s , ie' , ctxt-get-current-mod (toplevel-state.Γ s)) {- should not happen -}
        proceed s (just x) ie' with include-elt.need-to-add-symbols-to-context ie {- this indeed should be ie, not ie' -}
        proceed (mk-toplevel-state ip fns is Γ) (just x) ie' | tt
          with include-elt.do-type-check ie | ctxt-get-current-mod Γ 
        proceed (mk-toplevel-state ip fns is Γ) (just x) ie' | tt | do-check | prev-mod =
         let Γ = ctxt-initiate-file Γ filename (start-modname x) in
           process-start (mk-toplevel-state ip fns (trie-insert is filename ie') Γ)
                   filename pn x do-check Γ empty-spans ≫=monad cont
           where cont : toplevel-state × ctxt × spans → mF (toplevel-state × include-elt × mod-info)
                 cont (mk-toplevel-state ip fns is Γ , Γ' @ (mk-ctxt ret-mod _ _ _ _) , ss) =
                   progress-update pn do-check ≫monad returnM
                     (mk-toplevel-state ip (if do-check then (filename :: fns) else fns) is
                       (ctxt-set-current-mod Γ prev-mod) ,
                     (if do-check then set-spans-include-elt ie' ss else ie') , ret-mod)
        proceed s (just x) ie' | _ = returnM (s , ie' , ctxt-get-current-mod (toplevel-state.Γ s))

process-consts DataNull ps = spanMok
process-consts (DataCons (DataConst pi c tp) cs) ps =
      get-ctxt (λ Γ → 
        let t = abs-expand-type' ps tp in -- add-param-type ps (qualif-type Γ tp)
        check-type t (just star) ≫span 
        set-ctxt (ctxt-const-def pi c (qualif-type Γ t) Γ) ≫span
        spanM-add (DefDataConst-span pi c)  ≫span
        process-consts cs ps)



