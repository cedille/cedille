import cedille-options
open import general-util
open import lib

module process-cmd
  (options : cedille-options.options)
  {mF : Set → Set}
  {{_ : monad mF}}
  (progress-update : string → mF ⊤)
  (write-to-log : string → mF ⊤) where

--open import cedille-find
open import cedille-types
open import classify options {mF}
open import constants
open import conversion
open import ctxt
open import free-vars
open import rename
open import spans options {mF}
open import subst
open import syntax-util
open import type-util
open import toplevel-state options {mF}
open import datatype-functions
open import rewriting
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

check-and-add-params : ctxt → posinfo → ex-params → spanM (ctxt × params)
check-and-add-params Γ pi' (p@(ExParam pi1 me pi1' x atk pi2) :: ps') =
  Γ ⊢ atk ↝ atk~ /
  let Γ' = Γ , pi1' - x :` atk~ in
  [- punctuation-span "Parens (parameter)" pi1 pi2 -]
  [- Decl-span Γ' decl-param pi1 pi1' x atk~ me pi2 pi' -]
  [- var-span me Γ' pi1' x checking atk~ nothing -]
  check-and-add-params Γ' pi' ps' ≫=spanc λ Γ'' ps' →
  spanMr2 Γ'' (Param me x atk~ :: substh-params Γ'' (renamectxt-single (pi1' % x) x) empty-trie ps')
check-and-add-params Γ pi' [] = spanMr (Γ , [])

optAs-posinfo-var : ctxt → maybe import-as → posinfo × var → spanM (posinfo × var)
optAs-posinfo-var Γ nothing = spanMr
optAs-posinfo-var Γ (just (ImportAs pi x)) orig =
  [- Import-module-span Γ orig [] [ not-for-navigation ] nothing -]
  spanMr (pi , x)


{-# TERMINATING #-}
process-cmd : toplevel-state → ex-cmd → spanM (toplevel-state × cmd)
process-cmds : toplevel-state → ex-cmds → spanM (toplevel-state × cmds)
process-ctrs : var → type → posinfo → params → toplevel-state → ex-ctrs → spanM ((ctxt → ctxt) × ctrs)
process-params : toplevel-state → posinfo → ex-params → spanM (toplevel-state × params)
process-start : toplevel-state → filepath → (progress-name : string) → ex-file → spanM (toplevel-state × file)
process-file : toplevel-state → filepath → (progress-name : string) → mF (toplevel-state × file × mod-info)
 
process-cmd (mk-toplevel-state ip fns is Γ) (ExCmdDef op (ExDefTerm pi x (just tp) t) pi') =
  Γ ⊢ tp ⇐ KdStar ↝ tp' /
  Γ ⊢ t ⇐ tp' ↝ t' /
  check-erased-margs Γ (term-start-pos t) (term-end-pos t) t' (just tp') ≫span 
  let Γ' = ctxt-term-def pi globalScope op x (just t') tp' Γ in
  [- DefTerm-span Γ' pi x checking (just tp') t' pi' [] -]
  check-redefined pi x (mk-toplevel-state ip fns is Γ) (CmdDefTerm op x tp' t')
    ([- uncurry (Var-span Γ' pi x checking) (compileFail-in Γ t') -]
     spanMr (mk-toplevel-state ip fns is Γ'))

process-cmd (mk-toplevel-state ip fns is Γ) (ExCmdDef op (ExDefTerm pi x nothing t) pi') = 
  Γ ⊢ t ↝ t~ ⇒ T~ /
  check-erased-margs Γ (term-start-pos t) (term-end-pos t) t~ nothing ≫span 
  let Γ' = ctxt-term-def pi globalScope op x (just t~) T~ Γ in
  [- DefTerm-span Γ' pi x synthesizing (just T~) t~ pi' [] -]
  check-redefined pi x (mk-toplevel-state ip fns is Γ) (CmdDefTerm op x T~ t~)
    ([- uncurry (Var-span Γ' pi x synthesizing) (compileFail-in Γ t~) -]
     spanMr (mk-toplevel-state ip fns is Γ'))

process-cmd (mk-toplevel-state ip fns is Γ) (ExCmdDef op (ExDefType pi x k tp) pi') =
  Γ ⊢ k ↝ k~ /
  Γ ⊢ tp ⇐ k~ ↝ tp~ /
  let Γ' = ctxt-type-def pi globalScope op x (just tp~) k~ Γ in
  spanM-add (DefType-span Γ' pi x checking (just k~) tp~ pi' []) ≫span
  check-redefined pi x (mk-toplevel-state ip fns is Γ) (CmdDefType op x k~ tp~)
    ([- TpVar-span Γ' pi x checking [] nothing -]
     spanMr (mk-toplevel-state ip fns is Γ'))

{-
process-cmd (mk-toplevel-state ip fns is Γ) (DefTermOrType op (DefType pi x k tp) pi') ff {- skip checking -} = 
  let k' = qualif-kind Γ k in
    check-redefined pi x (mk-toplevel-state ip fns is Γ)
      (spanMr (mk-toplevel-state ip fns is (ctxt-type-def pi globalScope op x (just tp) k' Γ)))
-}

process-cmd (mk-toplevel-state ip fns is Γ) (ExCmdKind pi x ps k pi') =
  check-and-add-params Γ pi' ps ≫=spanc λ Γₚₛ ps~ →
  Γₚₛ ⊢ k ↝ k~ /
  let Γ' = ctxt-kind-def pi x ps~ k~ Γ in
  [- DefKind-span Γ' pi x k~ pi' -]
  check-redefined pi x (mk-toplevel-state ip fns is Γ') (CmdDefKind x ps~ k~)
    ([- KdVar-span Γ' (pi , x) (posinfo-plus-str pi x) ps~ checking [] nothing -]
     spanMr (mk-toplevel-state ip fns is Γ'))

process-cmd s (ExCmdData (DefDatatype pi pi' x ps k cs) pi'') =
  let Γ = toplevel-state.Γ s
      old-Γ = Γ in
  [- DefDatatype-header-span pi -]  
  check-and-add-params Γ pi'' ps ≫=spanc λ Γₚₛ ps' →
  Γₚₛ ⊢ k ↝ k' /
  let unqual-ps = map (λ {(ExParam pi me pi' x atk pi'') → pi' , x}) ps
      k' = subst-unqual Γ unqual-ps k'
      mn = ctxt-get-current-modname Γ
      qx = mn # x
      mps = ctxt-get-current-params Γ ++ ps'
      is = kind-to-indices Γₚₛ k'
      kᵢ = indices-to-kind is $ KdAbs ignored-var
             (Tkt $ indices-to-tpapps is $ params-to-tpapps mps $ TpVar qx) KdStar
      Γ-decl = λ Γ → ctxt-type-decl pi' x k' $ data-highlight Γ (pi' % x) in
  process-ctrs (pi' % x) (apps-type (TpVar qx) (params-to-args mps))
    pi' ps' (record s {Γ = Γ-decl Γₚₛ}) cs ≫=spanc λ Γ-cs cs~ →
  check-redefined pi' x (record s {Γ = Γ-cs Γ}) (CmdDefData x ps' k' cs~)
  let fₓ = fresh-var (add-indices-to-ctxt is Γ) "X"
      cs~ = map (λ {(Ctr x T) → Ctr (mn # x) T}) cs~
      Γ' = Γ-cs Γ  -- ctxt-restore-info* (elim-pair m $ ctxt-restore-info Γ x) ms
      kₘᵤ = abs-expand-kind ps' $ KdAbs ignored-var (Tkk k') KdStar
      Γ' = ctxt-type-def pi' globalScope opacity-open (data-Is/ x) nothing kₘᵤ Γ'
      Tₘᵤ = params-to-alls ps' $ TpApp (params-to-tpapps mps (TpVar (mn # data-Is/ x))) (Ttp (params-to-tpapps mps $ TpVar qx))
      Γ' = ctxt-term-def pi' globalScope opacity-open (data-is/ x) nothing Tₘᵤ Γ'
      Tₜₒ =
        abs-expand-type ps' $
        mall fₓ (Tkk $ indices-to-kind is KdStar) $
        TpAbs Erased ignored-var (Tkt (TpApp (params-to-tpapps mps $ TpVar $ mn # data-Is/ x) $ Ttp $ TpVar fₓ)) $
        indices-to-alls is $
        TpAbs NotErased ignored-var (Tkt (indices-to-tpapps is $ TpVar fₓ)) $
        indices-to-tpapps is $ params-to-tpapps mps $ TpVar qx
      Γ' = ctxt-term-def pi' globalScope opacity-open (data-to/ x) (just id-term) Tₜₒ Γ'
      Γ' = ctxt-datatype-def pi' x ps' kᵢ k' cs~ Γ' in
  [- DefDatatype-span Γ' pi pi' x ps' (abs-expand-kind ps' k') kₘᵤ k' Tₘᵤ Tₜₒ cs~ k pi'' -]
  [- TpVar-span Γ' pi' x checking (kind-data old-Γ k' :: params-data old-Γ ps') nothing -]
  spanMr (record s {Γ = Γ'})



-- TODO ignore checking but still gen spans if need-to-check false?
process-cmd s (ExCmdImport (ExImport pi op pi' x oa as pi'')) =
  let fnₒ = ctxt-get-current-filename (toplevel-state.Γ s)
      ie = get-include-elt s fnₒ
      oa' = maybe-map (λ {(ImportAs pi x) → x}) oa in
  case trie-lookup (include-elt.import-to-dep ie) x of λ where
    nothing → [- Import-span pi "missing" pi'' [] (just ("File not found: " ^ x)) -]
              spanMr2 (set-include-elt s fnₒ (record ie {err = tt}))
                      (CmdImport (Import op x oa' []))
    (just fnᵢ) ss →
      process-file s fnᵢ x ≫= uncurry λ s → uncurry λ f _ →
--      write-to-log ("syms:\n" ^ trie-to-string ": " (uncurry λ qv xs → qv ^ " defines " ^ 𝕃-to-string id ", " xs) (fst (ctxt.syms (toplevel-state.Γ s)))) ≫
        (process-import (toplevel-state.Γ s) op oa fnₒ fnᵢ
          (lookup-mod-params (toplevel-state.Γ s) fnᵢ)
          (maybe-else' (lookup-mod-params (toplevel-state.Γ s) fnₒ) [] id)
         ≫=spanc λ e as~ →
         let s-e = scope-file s fnₒ fnᵢ oa' as~ in
         [- Import-span pi fnᵢ pi'' [] (snd s-e maybe-or e) -]
         spanMr2 (fst s-e) (CmdImport (Import op x oa' as~))) ss
  where
  -- When importing a file publicly, you may use any number of arguments as long as the
  -- parameters of the current module are not free in them.
  -- You may then use any number of single-variable parameters from the current module
  -- as arguments as long as they retain the same order as before and have no non-parameter
  -- arguments between them
  -- (so parameters A, B, C, ..., Z can be used as arguments ·C ·X, but not ·X ·C)
  public-import-params-ok : params → args → err-m
  public-import-params-ok ps = h nothing where
    err = just "You can only use parameters for arguments to public imports if the are in order at the end"
    params-order : params → trie ℕ
    params-order = h 0 where
      h : ℕ → params → trie ℕ
      h n [] = empty-trie
      h n (Param me x atk :: ps) = trie-insert (h (suc n) ps) x n
    pso = params-order ps
    ps-free : arg → err-m → err-m
    ps-free a e = if ~ are-free-in-h pso (free-vars-arg a) then e else err
    h : maybe ℕ → args → err-m
    h c (a :: as) =
      maybe-else' (arg-var a ≫=maybe trie-lookup pso)
        (maybe-else' c (ps-free a $ h nothing as) λ _ → err) λ aₙ →
      maybe-else' c (h (just aₙ) as) λ cₙ →
      if cₙ ≥ aₙ then err else h (just aₙ) as
    h n [] = nothing
  
  process-import : ctxt → opt-public → maybe import-as → (cur imp : filepath) → maybe params → params → spanM (err-m × args)
  process-import Γ op oa fnₒ fnᵢ nothing _ = spanMr2 (just "Undefined module import (this probably shouldn't happen?)") []
  process-import Γ Public (just _) fnₒ fnᵢ (just psᵢ) psₒ = spanMr2 (just "Public imports aren't allowed to be qualified") []
  process-import Γ op oa fnₒ fnᵢ (just psᵢ) psₒ =
    optAs-posinfo-var Γ oa (pi' , x) ≫=span λ pi-v →
    check-args Γ as psᵢ ≫=span λ as~ →
    [- Import-module-span Γ (pi' , x) psᵢ [ location-data (fnᵢ , "1") ] nothing -]
    spanMr2 (maybe-if op ≫maybe public-import-params-ok psₒ as~) as~



-- the call to ctxt-update-symbol-occurrences is for cedille-find functionality
process-cmds s (c :: cs) =
  process-cmd s c ≫=spanc λ s c →
  process-cmds s cs ≫=spanc λ s cs →
  spanMr2 s (c :: cs)
process-cmds s [] = spanMr2 s []

process-ctrs X Xₜ piₓ ps s csₒ c? = h s csₒ c? where
  h : toplevel-state → ex-ctrs → spanM ((ctxt → ctxt) × ctrs)
  h s [] = spanMr2 id []
  h s (ExCtr pi x T :: cs) =
    let Γ = toplevel-state.Γ s in
    Γ ⊢ T ⇐ KdStar ↝ T~ /
    let T = hnf-ctr Γ X T~
        neg-ret-err = ctr-positive Γ X T ≫=maybe λ neg-ret →
          let err-msg = if neg-ret
                          then " occurs negatively in the"
                          else " is not the return" in
          just (unqual-local X ^ err-msg ^ " type of the constructor")
        T = subst Γ Xₜ X T in
    h s cs ≫=spanc λ Γ-f cs →
    let Γ = toplevel-state.Γ s
        Γ-f' = ctxt-ctr-def pi x T ps (length csₒ) (length csₒ ∸ suc (length cs)) in
    check-redefined pi x s (Ctr x T :: cs)
      (let Γ = Γ-f' Γ in
       [- Var-span Γ pi x checking
            [ summary-data x (ctxt-type-def piₓ globalScope opacity-open
                (unqual-local X) nothing KdStar Γ) (abs-expand-type ps T) ] neg-ret-err -]
       spanMr (record s {Γ = Γ})) ≫=spanc λ s cs →
    spanMr2 (Γ-f ∘ Γ-f') cs

process-params s pi ps =
  let Γ = toplevel-state.Γ s in
  check-and-add-params Γ pi ps ≫=spanc λ Γₚₛ ps →
  spanMr2
    (record s {Γ = ctxt-add-current-params (ctxt-set-current-params Γₚₛ ps)})
    ps

process-start s filename pn (ExModule is pi1 pi2 mn ps cs pi3) =
  spanM-push (progress-update pn) ≫span
  process-cmds s (map ExCmdImport is) ≫=spanc λ s is' →
  process-params s (params-end-pos first-position ps) ps ≫=spanc λ s ps →
  process-cmds s cs ≫=spanc λ s cs → 
  process-cwst s filename ≫=span λ s →
  let pi2' = posinfo-plus-str pi2 mn in
  [- File-span (toplevel-state.Γ s) first-position (posinfo-plus pi3 1) filename -]
  [- Module-span pi2 pi2' -]
  [- Module-header-span pi1 pi2' -]
  spanMr2 s (Module (cmds-to-imps is') mn ps cs)

{- process (type-check if necessary) the given file.  
   We assume the given top-level state has a syntax tree associated with the file. -}
process-file s filename pn with get-include-elt s filename
process-file s filename pn | ie =
  proceed s (include-elt.ast ie) (include-elt.ast~ ie)
      (set-need-to-add-symbols-to-context-include-elt ie ff) ≫= λ where
    (s , ie , ret-mod , f) → returnM ({-set-include-elt s filename ie-} s , f , ret-mod)
  where
  proceed : toplevel-state → maybe ex-file → maybe file → include-elt →
            mF (toplevel-state × include-elt × mod-info × file)
  proceed s nothing f~ ie' =
    progress-update filename ≫
--    write-to-log "should not happen" ≫
    returnM (s , ie' , ctxt-get-current-mod (toplevel-state.Γ s) ,
             maybe-else' f~ (Module [] ignored-var [] []) id) {- should not happen -}
  proceed s (just x) f~ ie' with include-elt.need-to-add-symbols-to-context ie
  proceed (mk-toplevel-state ip fns is Γ) (just x) f~ ie' | tt
    with include-elt.do-type-check ie | ctxt-get-current-mod Γ
  proceed (mk-toplevel-state ip fns is Γ) (just x) f~ ie' | tt | do-check | prev-mod =
   let Γ = ctxt-initiate-file Γ filename (start-modname x) in
     process-start (mk-toplevel-state ip fns (trie-insert is filename ie') Γ)
             filename pn x empty-spans ≫= λ where
       ((mk-toplevel-state ip fns is Γ @ (mk-ctxt ret-mod _ _ _) , f) , ss) →
         let ie'' = if do-check then (record (set-spans-include-elt ie' ss) { ast~ = just f }) else record ie' { ast~ = include-elt.ast~ ie' maybe-or just f } in
         progress-update pn ≫ returnM
           (mk-toplevel-state ip (if do-check then (filename :: fns) else fns) (trie-insert is filename ie'')
             (ctxt-set-current-mod Γ prev-mod) ,
            ie'' ,
            ret-mod ,
            f)
  proceed s (just x) f~ ie' | _ =
--    write-to-log ("already checked " ^ ctxt-get-current-filename (toplevel-state.Γ s)) ≫
    returnM (s , ie' , ctxt-get-current-mod (toplevel-state.Γ s) ,
             maybe-else' f~ (Module [] ignored-var [] []) id)

