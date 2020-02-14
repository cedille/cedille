import cedille-options
open import general-util

module process-cmd
  (options : cedille-options.options)
  {mF : Set → Set}
  {{mFm : monad mF}}
  (progress-update : string → mF ⊤)
  (write-to-log : string → mF ⊤) where

--open import cedille-find
open import cedille-types
open import classify options {mF} ⦃ mFm ⦄ write-to-log
open import constants
open import conversion
open import ctxt
open import free-vars
open import rename
open import spans options { mF } ⦃ mFm ⦄
open import subst
open import syntax-util
open import type-util
open import toplevel-state options { mF } ⦃ mFm ⦄
open import to-string options

open import datatype-util
open import rewriting
open import elab-util options
import cws-types
import cws

-- generate spans from the given comments-and-whitespace syntax tree 
process-cwst-etys : cws-types.entities → spanM ⊤
process-cwst-ety : cws-types.entity → spanM ⊤
process-cwst-etys (cws-types.Entity ety etys) = process-cwst-ety ety >> process-cwst-etys etys
process-cwst-etys cws-types.EndEntity = return triv
process-cwst-ety cws-types.EntityNonws = return triv
process-cwst-ety (cws-types.EntityWs pi pi') = return triv
process-cwst-ety (cws-types.EntityComment pi pi') = [- comment-span pi pi' -] return triv

process-cwst : toplevel-state → filepath → spanM toplevel-state
process-cwst s filename with include-elt.cwst (get-include-elt s filename)
process-cwst s filename | nothing = return s
process-cwst s filename | just (cws-types.File etys) = process-cwst-etys etys >> return s

check-and-add-params : ctxt → posinfo → ex-params → spanM (ctxt × params)
check-and-add-params Γ pi' (p@(ExParam pi1 me pi1' x atk pi2) :: ps') =
  Γ ⊢ atk ↝ atk~ /
  let Γ' = Γ , pi1' - x :` atk~
      qx = pi1' % x in
  [- punctuation-span "Parens (parameter)" pi1 pi2 -]
  [- Decl-span Γ' decl-param pi1 pi1' x atk~ me pi2 pi' -]
  [- var-span me Γ' pi1' x checking atk~ nothing -]
  check-and-add-params Γ' pi' ps' >>=c λ Γ'' ps~ →
  return2 Γ'' (Param me qx atk~ :: ps~)
check-and-add-params Γ pi' [] = return2 Γ []

optAs-posinfo-var : ctxt → maybe import-as → posinfo × var → spanM (posinfo × var)
optAs-posinfo-var Γ nothing = return
optAs-posinfo-var Γ (just (ImportAs pi x)) orig =
  [- Import-module-span Γ orig [] [ not-for-navigation ] nothing -]
  return2 pi x


{-# TERMINATING #-}
{- notice that these are elaborating functions: they take an ex-QQQ and return a QQQ (along with other activity) -}
process-cmd : toplevel-state → ex-cmd → spanM (toplevel-state × cmd)
process-cmds : toplevel-state → ex-cmds → spanM (toplevel-state × cmds)
process-ctrs : (uqv lqv mqv : var) → params → posinfo → toplevel-state → ex-ctrs → spanM ((ctxt → ctxt) × ctrs)
process-params : toplevel-state → posinfo → ex-params → spanM (toplevel-state × params)
process-start : toplevel-state → filepath → (progress-name : string) → ex-file → spanM (toplevel-state × file)
process-file : toplevel-state → filepath → (progress-name : string) → mF (toplevel-state × file × string × string × params × qualif)

maybe-add-opaque-span : optopaque → (end : posinfo) → spanM ⊤
maybe-add-opaque-span nothing pi = return triv
maybe-add-opaque-span (just piₒ) pi =
  spanM-add $ Opaque-span piₒ pi

process-cmd s (ExCmdDef op (ExDefTerm pi x (just tp) t) pi') =
  let Γ = toplevel-state.Γ s in
  Γ ⊢ tp ⇐ KdStar ↝ tp' /
  Γ ⊢ t ⇐ tp' ↝ t' /
  check-erased-margs Γ (term-start-pos t) (term-end-pos t) t' (just tp') >>
  let Γ' = ctxt-term-def pi globalScope (isNothing op) x (just t') tp' Γ in
  maybe-add-opaque-span op pi' >>
  [- DefTerm-span Γ' pi x checking (just tp') t' pi' [] -]
  check-redefined pi x s
    (CmdDefTerm x t')
    ([- uncurry (Var-span Γ' pi x checking) (compileFail-in Γ t') -]
     return (record s { Γ = Γ' }))

process-cmd s (ExCmdDef op (ExDefTerm pi x nothing t) pi') = 
  let Γ = toplevel-state.Γ s in
  Γ ⊢ t ↝ t~ ⇒ T~ /
  check-erased-margs Γ (term-start-pos t) (term-end-pos t) t~ nothing >> 
  let Γ' = ctxt-term-def pi globalScope (isNothing op) x (just t~) T~ Γ in
  maybe-add-opaque-span op pi' >>
  [- DefTerm-span Γ' pi x synthesizing (just T~) t~ pi' [] -]
  check-redefined pi x s
    (CmdDefTerm x t~)
    ([- uncurry (Var-span Γ' pi x synthesizing) (compileFail-in Γ t~) -]
     return (record s { Γ = Γ' }))

process-cmd s (ExCmdDef op (ExDefType pi x k tp) pi') =
  let Γ = toplevel-state.Γ s in
  Γ ⊢ k ↝ k~ /
  Γ ⊢ tp ⇐ k~ ↝ tp~ /
  let Γ' = ctxt-type-def pi globalScope (isNothing op) x (just tp~) k~ Γ in
  maybe-add-opaque-span op pi' >>
  spanM-add (DefType-span Γ' pi x checking (just k~) tp~ pi' []) >>
  check-redefined pi x s
    (CmdDefType x k~ tp~)
    ([- TpVar-span Γ' pi x checking [] nothing -]
     return (record s { Γ = Γ' }))

process-cmd s (ExCmdKind pi x ps k pi') =
  let Γ = toplevel-state.Γ s in
  check-and-add-params Γ pi' ps >>=c λ Γₚₛ ps~ →
  Γₚₛ ⊢ k ↝ k~ /
  let Γ' = ctxt-kind-def pi x ps~ k~ Γ in
  [- DefKind-span Γ' pi x k~ pi' -]
  check-redefined pi x s (CmdDefKind x ps~ k~)
    ([- KdVar-span Γ' (pi , x) (posinfo-plus-str pi x) ps~ checking [] nothing -]
     return (record s { Γ = Γ' }))

process-cmd s (ExCmdData (DefDatatype pi pi' x ps k cs) pi'') =
  let Γ = toplevel-state.Γ s
      old-Γ = Γ in
  [- DefDatatype-header-span pi -]  
  check-and-add-params Γ pi'' ps >>=c λ Γₚₛ ps' →
  Γₚₛ ⊢ k ↝ k' /
  let mn = ctxt.mn Γ
      qx = mn # x
      mps = ctxt.ps Γ ++ ps'
      Γ-decl = λ Γ → ctxt-type-decl pi' x k' $ data-highlight Γ (pi' % x)
      cmd-fail = CmdDefType x (params-to-kind ps' k') (TpHole pi')
      fail = λ e → [- TpVar-span Γ pi' x checking [] (just e) -] return2 s cmd-fail in
  process-ctrs x (pi' % x) qx mps pi' (record s {Γ = Γ-decl Γₚₛ}) cs >>=c λ Γ-cs cs~ →
  maybe-else' (cedille-options.options.datatype-encoding options >>=c λ fp f → f)
    (fail "Missing directive for datatype encoding.  Please add a datatype-encoding directive to your .cedille/options file. See cedille/.cedille/options for the current location") λ de →
  let is = kind-to-indices Γₚₛ k'
      kᵢ = indices-to-kind is $ KdAbs ignored-var
             (Tkt $ indices-to-tpapps is $ params-to-tpapps mps $ TpVar qx) KdStar in
  either-else' (init-encoding Γₚₛ de (Data x ps' is cs~)) fail λ ecs →
  check-redefined pi' x (record s {Γ = Γ-cs Γ}) (CmdDefData ecs x ps' k' cs~)
  let fₓ = fresh-var (add-indices-to-ctxt is Γ) "X"
      cs~ = map-fst (mn #_) <$> cs~
      Γ' = Γ-cs Γ
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
      Γ' = ctxt-datatype-def pi' x ps' kᵢ k' cs~ ecs Γ' in
  [- DefDatatype-span Γ' pi pi' x ps' (abs-expand-kind ps' k') kₘᵤ k' Tₘᵤ Tₜₒ cs~ k pi'' -]
  [- TpVar-span Γ' pi' x checking (kind-data old-Γ k' :: params-data old-Γ ps') nothing -]
  return (record s {Γ = Γ'})



-- TODO ignore checking but still gen spans if need-to-check false?
process-cmd s (ExCmdImport (ExImport pi op pi' x oa as pi'')) =
  let fnₒ = ctxt.fn (toplevel-state.Γ s)
      ie = get-include-elt s fnₒ
      oa' = maybe-map (λ {(ImportAs pi x) → x}) oa in
  case trie-lookup (include-elt.import-to-dep ie) x of λ where
    nothing → [- Import-span pi "missing" pi'' [] (just ("File not found: " ^ x)) -]
              return2 (set-include-elt s fnₒ (record ie {err = tt}))
                      (CmdImport (Import op x x oa' []))
    (just fnᵢ) →
      spanM-push (process-file s fnᵢ x) >>= uncurry₂ λ s f _ →
        process-import (toplevel-state.Γ s) op oa fnₒ fnᵢ
          (lookup-mod-params (toplevel-state.Γ s) fnᵢ)
          (maybe-else' (lookup-mod-params (toplevel-state.Γ s) fnₒ) [] id) >>=c λ e as~ →
         let s-e = scope-file s fnₒ fnᵢ oa' as~
             Γ = toplevel-state.Γ s in
         [- Import-span pi fnᵢ pi'' [] (snd s-e ||-maybe e) -]
         return2 (fst s-e) (CmdImport (Import op fnᵢ x oa' as~))
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
      maybe-else' (arg-var a >>= trie-lookup pso)
        (maybe-else' c (ps-free a $ h nothing as) λ _ → err) λ aₙ →
      maybe-else' c (h (just aₙ) as) λ cₙ →
      if cₙ ≥ aₙ then err else h (just aₙ) as
    h n [] = nothing
  
  process-import : ctxt → opt-public → maybe import-as → (cur imp : filepath) → maybe params → params → spanM (err-m × args)
  process-import Γ op oa fnₒ fnᵢ nothing _ = return2 (just "Undefined module import (this probably shouldn't happen?)") []
  process-import Γ Public (just _) fnₒ fnᵢ (just psᵢ) psₒ = return2 (just "Public imports aren't allowed to be qualified") []
  process-import Γ op oa fnₒ fnᵢ (just psᵢ) psₒ =
    optAs-posinfo-var Γ oa (pi' , x) >>= λ pi-v →
    check-args Γ as psᵢ >>= λ as~ →
    [- Import-module-span Γ (pi' , x) psᵢ [ location-data (fnᵢ , "1") ] nothing -]
    return2 (ifMaybe op $ public-import-params-ok psₒ as~) as~



process-cmds s (c :: cs) =
  process-cmd s c >>=c λ s c →
  process-cmds s cs >>=c λ s cs →
  return2 s (c :: cs)
process-cmds s [] = return2 s []

process-ctrs uX lX mX ps piₓ s csₒ c? = h s csₒ c? where
  h : toplevel-state → ex-ctrs → spanM ((ctxt → ctxt) × ctrs)
  h s [] = return2 id []
  h s (ExCtr pi x T :: cs) =
    let Γ = toplevel-state.Γ s in
    Γ ⊢ T ⇐ KdStar ↝ T~ /
    let T = hnf-ctr Γ lX T~
        𝕃tpkd-to-string = foldr (λ tk s → rope-to-string (tpkd-to-string Γ tk) ^ " ; " ^ s) ""
        neg-ret-err : maybe string
        neg-ret-err =
          let err-msg = λ s s' → just (uX ^ s ^ " type of the constructor: " ^ s') in
            case run-posM (positivity.ctr-positive lX Γ T) of
              λ where
                (ctorOk , l) → nothing
                (ctorNegative , l) → err-msg " occurs negatively in the"
                                       ("Searching types: " ^ 𝕃tpkd-to-string l)
                (ctorNotInReturnType , l) → err-msg " is not the return" "" in
    let T = [ Γ - TpVar mX / lX ] T
        Tₚₛ = [ Γ - params-to-tpapps ps (TpVar mX) / lX ] T~ in
    h s cs >>=c λ Γ-f cs →
    let Γ = toplevel-state.Γ s
        Γ-f' = ctxt-ctr-def pi x Tₚₛ ps (length csₒ) (length csₒ ∸ suc (length cs)) in
    check-redefined pi x s (Ctr x T :: cs)
      (let Γ = Γ-f' Γ in
         [- Var-span Γ pi x checking
             [ summary-data x (ctxt-type-def piₓ globalScope opacity-open uX nothing KdStar Γ)
                 (abs-expand-type ps T) ] neg-ret-err -]
       return (record s {Γ = Γ})) >>=c λ s →
    return2 (Γ-f ∘ Γ-f')

process-params s pi ps =
  let Γ = toplevel-state.Γ s in
  check-and-add-params Γ pi ps >>=c λ Γₚₛ ps →
  return2
    (record s {Γ = ctxt-add-current-params (record Γₚₛ { ps = ps })})
    ps

process-start s filename pn (ExModule is pi1 pi2 mn ps cs pi3) =
  spanM-push (progress-update pn) >>
  process-cmds s (map ExCmdImport is) >>=c λ s is' →
  process-params s (params-end-pos first-position ps) ps >>=c λ s ps →
  process-cmds s cs >>=c λ s cs →
  process-cwst s filename >>= λ s →
  let pi2' = posinfo-plus-str pi2 mn in
  [- File-span (toplevel-state.Γ s) first-position (posinfo-plus pi3 1) filename -]
  [- Module-span pi2 pi2' -]
  [- Module-header-span pi1 pi2' -]
  return2 s (Module mn ps (is' ++ cs))
--  where
--  unqual-cmd : ctxt → renamectxt → cmd → cmd
--  unqual-cmd Γ ρ (CmdDefTerm x t) = CmdDefTerm x (subst-renamectxt Γ ρ t)
--  unqual-cmd Γ ρ (CmdDefType x k T) = CmdDefType x (subst-renamectxt Γ ρ k) (subst-renamectxt Γ ρ T)
--  unqual-cmd Γ ρ (CmdDefKind x ps k) = CmdDefKind x (substh-params Γ ρ empty-trie ps) (subst-renamectxt (add-params-to-ctxt ps Γ) ρ k)
--  unqual-cmd Γ ρ (CmdDefData eds x ps k cs) = CmdDefData eds x (substh-params Γ ρ empty-trie ps) (subst-renamectxt (add-params-to-ctxt ps Γ) ρ k) (map-snd (subst-renamectxt (add-params-to-ctxt ps Γ) ρ) <$> cs)
--  unqual-cmd Γ ρ (CmdImport (Import op fnᵢ x oa as)) = CmdImport (Import op fnᵢ x oa (subst-renamectxt Γ ρ -arg_ <$> as))

{- process (type-check if necessary) the given file.  
   We assume the given top-level state has a syntax tree associated with the file. -}
process-file s filename pn with get-include-elt s filename
process-file s filename pn | ie =
  proceed s (include-elt.ast ie) (include-elt.ast~ ie)
      (set-need-to-add-symbols-to-context-include-elt ie ff) >>= λ where
    (s , ie , ret-mod , f) → return ({-set-include-elt s filename ie-} s , f , ret-mod)
  where
  proceed : toplevel-state → maybe ex-file → maybe file → include-elt →
            mF (toplevel-state × include-elt × (string × string × params × qualif) × file)
  proceed s nothing f~ ie' =
    progress-update filename >>
--    write-to-log "should not happen" >>
    return (s , ie' , ctxt-get-current-mod (toplevel-state.Γ s) ,
             maybe-else' f~ (Module ignored-var [] []) id) {- should not happen -}
  proceed s (just x) f~ ie' with include-elt.need-to-add-symbols-to-context ie
  proceed s (just x) (just f~) ie' | ff =
    let Γ = toplevel-state.Γ s
        mod = ctxt.fn Γ , ctxt.mn Γ , ctxt.ps Γ , ctxt.qual Γ in
    return (s , ie' , mod , f~)
  proceed (mk-toplevel-state ip fns is Γ logFilePath) (just x) f~ ie' | _
    with include-elt.do-type-check ie | ctxt-get-current-mod Γ
  proceed (mk-toplevel-state ip fns is Γ logFilePath) (just x) f~ ie' | _ | do-check | prev-mod =
   let Γ = ctxt-initiate-file Γ filename (start-modname x) in
     process-start (mk-toplevel-state ip fns (trie-insert is filename ie') Γ logFilePath)
             filename pn x empty-spans >>= λ where
       ((mk-toplevel-state ip fns is Γ logFilePath , f) , ss) →
         let ret-mod = ctxt.fn Γ , ctxt.mn Γ , ctxt.ps Γ , ctxt.qual Γ
             ie'' = if do-check then set-spans-include-elt ie' ss f else record ie' { ast~ = include-elt.ast~ ie' ||-maybe just f } in
         progress-update pn >> return
           (mk-toplevel-state ip (if do-check then (filename :: fns) else fns) (trie-insert is filename ie'')
             (ctxt-set-current-mod Γ prev-mod) logFilePath ,
            ie'' ,
            ret-mod ,
            f)
--  proceed s (just x) f~ ie' | ff =
--    return (s , ie' , ctxt-get-current-mod (toplevel-state.Γ s) ,
--             maybe-else' f~ (Module ignored-var [] []) id)

