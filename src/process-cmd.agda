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
open import is-free
open import rename
open import spans options {mF}
open import subst
open import syntax-util
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

process-t : Set → Set
process-t X = toplevel-state → X → (need-to-check : 𝔹) → spanM toplevel-state

check-and-add-params : posinfo → params → spanM (𝕃 (string × restore-def))
check-and-add-params pi' (p@(Decl pi1 pi1' me x atk pi2) :: ps') =
  check-tk atk ≫span
  add-tk' me pi1' x atk ≫=span λ mi →
  get-ctxt λ Γ →
  spanM-add (Decl-span Γ param pi1 pi1' x atk me pi' {- make this span go to the end of the def, so nesting will work
                                              properly for computing the context in the frontend -}) ≫span
  check-and-add-params pi' ps' ≫=span λ ms → spanMr ((x , mi) :: ms)
check-and-add-params _ [] = spanMr []

dont-check-and-add-params : posinfo → params → spanM (𝕃 (string × restore-def))
dont-check-and-add-params pi' (p@(Decl pi1 pi1' me x atk pi2) :: ps') =
  add-tk' me pi1' x atk ≫=span λ mi →
  dont-check-and-add-params pi' ps' ≫=span λ ms → spanMr ((x , mi) :: ms)
dont-check-and-add-params _ [] = spanMr []

optAs-posinfo-var : optAs → (posinfo × var) → spanM (posinfo × var)
optAs-posinfo-var NoOptAs = spanMr
optAs-posinfo-var (SomeOptAs pi x) orig = get-ctxt λ Γ →
  spanM-add (Import-module-span Γ orig [] [ not-for-navigation ] nothing) ≫span spanMr (pi , x)


{-# TERMINATING #-}
process-cmd : process-t cmd
process-cmds : process-t cmds
process-ctrs : var → type → posinfo → params → process-t ctrs
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
    let Γ' = ctxt-term-def pi globalScope op x (just t) tp' Γ in
      spanM-add (DefTerm-span Γ' pi x checking (just tp) t pi' []) ≫span
      check-redefined pi x (mk-toplevel-state ip fns is Γ)
        (spanM-add (uncurry (Var-span Γ' pi x checking) (compileFail-in Γ t)) ≫span
         spanMr (mk-toplevel-state ip fns is Γ')))

process-cmd (mk-toplevel-state ip fns is Γ) (DefTermOrType op (DefTerm pi x (SomeType tp) t) pi') ff {- skip checking -} =
  let tp' = qualif-type Γ tp in
    check-redefined pi x (mk-toplevel-state ip fns is Γ)
      (spanMr (mk-toplevel-state ip fns is (ctxt-term-def pi globalScope op x (just t) tp' Γ)))


process-cmd (mk-toplevel-state ip fns is Γ) (DefTermOrType op (DefTerm pi x NoType t) pi') _ = 
  set-ctxt Γ ≫span
  check-term t nothing ≫=span λ mtp → 
  check-erased-margs t nothing ≫span 
  get-ctxt (λ Γ → 
      let Γ' = maybe-else
                 (ctxt-term-udef pi globalScope op x t Γ)
                 (λ tp → ctxt-term-def pi globalScope op x (just t) tp Γ) mtp in
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
      let Γ' = ctxt-type-def pi globalScope op x (just tp) k' Γ in
        spanM-add (DefType-span Γ' pi x checking (just k) tp pi' []) ≫span
        check-redefined pi x (mk-toplevel-state ip fns is Γ)
          (spanM-add (TpVar-span Γ' pi x checking [] nothing) ≫span
           spanMr (mk-toplevel-state ip fns is Γ')))


process-cmd (mk-toplevel-state ip fns is Γ) (DefTermOrType op (DefType pi x k tp) pi') ff {- skip checking -} = 
  let k' = qualif-kind Γ k in
    check-redefined pi x (mk-toplevel-state ip fns is Γ)
      (spanMr (mk-toplevel-state ip fns is (ctxt-type-def pi globalScope op x (just tp) k' Γ)))

process-cmd (mk-toplevel-state ip fns is Γ) (DefKind pi x ps k pi') tt {- check -} =
  set-ctxt Γ ≫span
  check-and-add-params pi' ps ≫=span λ ms → 
  check-kind k ≫span
  get-ctxt (λ Γ → 
    let Γ' = ctxt-kind-def pi x ps k Γ in
      spanM-add (DefKind-span Γ' pi x k pi') ≫span
      check-redefined pi x (mk-toplevel-state ip fns is Γ)
       (spanM-add (KndVar-span Γ' (pi , x) (posinfo-plus-str pi x) ps checking [] nothing) ≫span
        spanMr (mk-toplevel-state ip fns is (ctxt-restore-info* Γ' ms))))


process-cmd (mk-toplevel-state ip fns is Γ) (DefKind pi x ps k pi') ff {- skip checking -} = 
  set-ctxt Γ ≫span
  dont-check-and-add-params pi' ps ≫=span λ ms → 
  get-ctxt (λ Γ → 
    let Γ' = ctxt-kind-def pi x ps k Γ in
      check-redefined pi x (mk-toplevel-state ip fns is Γ)
        (spanMr (mk-toplevel-state ip fns is (ctxt-restore-info* Γ' ms))))

process-cmd s (DefDatatype (Datatype pi pi' x ps k cs) pi'') b{-tt-}  =
  let Γ = toplevel-state.Γ s in
  set-ctxt Γ ≫span
  spanM-add (DefDatatype-header-span pi) ≫span
  get-ctxt λ old-Γ →
  spanM-lookup-restore-info x ≫=span λ m →
  check-and-add-params pi'' ps ≫=span λ ms →
  get-ctxt λ Γ →
  check-kind k ≫span
  let --Γ' = foldr (λ {(Decl _ piₚ me x atk _) → ctxt-tk-decl piₚ x atk}) Γ ps
      mn = ctxt-get-current-modname Γ
      qx = mn # x
      ps = qualif-params old-Γ ps
      mps = ctxt-get-current-params Γ ++ ps
      k' = qualif-kind Γ k
      is = kind-to-indices Γ k'
      kᵢ = indices-to-kind is $ KndTpArrow
             (indices-to-tpapps is $ params-to-tpapps mps $ mtpvar qx) star in
  check-redefined pi' x s
    (set-ctxt (ctxt-type-decl pi' x k Γ) ≫span get-ctxt λ Γ →
     process-ctrs (qualif-var Γ x) (apps-type (mtpvar qx) (params-to-args mps))
       pi' ps (record s {Γ = Γ}) cs tt ≫span
     get-ctxt λ Γ →
     let fₓ = fresh-var "X" (ctxt-binds-var Γ) empty-renamectxt
         Γ' = ctxt-restore-info* (elim-pair m $ ctxt-restore-info Γ x) ms
         kₘᵤ = abs-expand-kind ps $ KndArrow k' star
         --Γ' = ctxt-type-def pi' globalScope OpacTrans (mu-name-Mu x) nothing kₘᵤ Γ'
         Γ' = ctxt-type-def pi' globalScope OpacTrans (data-Is/ x) nothing kₘᵤ Γ'
         Tₘᵤ = params-to-alls ps $ TpApp (params-to-tpapps mps (mtpvar (mn # data-Is/ x))) (params-to-tpapps mps $ mtpvar qx)
         Γ' = ctxt-term-def pi' globalScope OpacTrans (data-is/ x) nothing Tₘᵤ Γ'
         Tₜₒ =
           abs-expand-type ps $
           mall fₓ (Tkk $ indices-to-kind is star) $
           TpArrow (TpApp (params-to-tpapps mps $ mtpvar $ mn # data-Is/ x) $
                      mtpvar fₓ) Erased $
           indices-to-alls is $
           TpArrow (indices-to-tpapps is $ mtpvar fₓ) NotErased $
           indices-to-tpapps is $ params-to-tpapps mps $ mtpvar qx
         Γ' = ctxt-term-def pi' globalScope OpacTrans (data-to/ x) (just id-term) Tₜₒ Γ'
         cs' = flip map cs λ {(Ctr pi x' T) →
           Ctr posinfo-gen (mn # x') $ subst Γ (params-to-tpapps mps (mtpvar qx))
             (qualif-var Γ x) (hnf-ctr Γ (qualif-var Γ x) (qualif-type Γ T))}
         Γ' = ctxt-datatype-def pi' x ps kᵢ k' cs' Γ' in
     set-ctxt Γ' ≫span
     spanM-add (DefDatatype-span Γ' pi pi' x ps (qualif-kind Γ (abs-expand-kind ps k)) kₘᵤ (qualif-kind Γ k) Tₘᵤ Tₜₒ cs pi'') ≫span
     get-ctxt λ Γ →
     spanM-add (TpVar-span Γ pi' x checking
       (kind-data old-Γ k :: params-data old-Γ ps) nothing) ≫span
     spanMr (record s {Γ = Γ}))

{-process-cmd s (DefDatatype (Datatype pi pi' x ps k cs pi'') pi''') ff =
  spanMr s-}

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
         process-import op oa fnₒ fnᵢ (lookup-mod-params (toplevel-state.Γ s) fnᵢ) (maybe-else' (lookup-mod-params (toplevel-state.Γ s) fnₒ) [] id) ≫=span λ e →
         spanM-add (Import-span pi fnᵢ pi'' [] (snd s-e maybe-or e)) ≫span spanMr (fst s-e)) Γ ss
  where
  -- When importing a file publicly, you may use any number of arguments as long as the
  -- parameters of the current module are not free in them.
  -- You may then use any number of single-variable parameters from the current module
  -- as arguments as long as they retain the same order as before and have no non-parameter
  -- arguments between them
  -- (so parameters A, B, C, ..., Z can be used as arguments ∙ C ∙ X, but not ∙ X ∙ C)
  public-import-params-ok : params → args → err-m
  public-import-params-ok ps = h nothing where
    err = just "You can only use parameters for arguments to public imports if the are in order at the end"
    params-order : params → trie ℕ
    params-order = h 0 where
      h : ℕ → params → trie ℕ
      h n [] = empty-trie
      h n ((Decl _ _ me x atk _) :: ps) = trie-insert (h (suc n) ps) x n
    arg-var : arg → maybe var
    arg-var (TermArg me (Var pi x)) = just x
    arg-var (TypeArg (TpVar pi x)) = just x
    arg-var _ = nothing
    pso = params-order ps
    ps-free : arg → err-m → err-m
    ps-free a e = if ~ are-free-in-args check-erased pso [ a ] then e else err
    h : maybe ℕ → args → err-m
    h c (a :: as) =
      maybe-else' (arg-var a ≫=maybe trie-lookup pso)
        (maybe-else' c (ps-free a $ h nothing as) λ _ → err) λ aₙ →
      maybe-else' c (h (just aₙ) as) λ cₙ →
      if cₙ ≥ aₙ then err else h (just aₙ) as
    h n [] = nothing

  
  process-import : optPublic → optAs → (cur imp : filepath) → maybe params → params → spanM err-m
  process-import op oa fnₒ fnᵢ nothing _ = spanMr (just "Undefined module import (this probably shouldn't happen?)")
  -- process-import op oa fnₒ fnᵢ (just psᵢ) nothing = spanMr (just "Current module undefined (this shouldn't happen!)")
  process-import IsPublic (SomeOptAs _ _) fnₒ fnᵢ (just psᵢ) {-(just-} psₒ {-)-} = spanMr (just "Public import aren't allowed to be qualified")
  process-import op oa fnₒ fnᵢ (just psᵢ) {-(just-} psₒ {-)-} =
    optAs-posinfo-var oa (pi' , x) ≫=span λ pi-v →
    with-ctxt (toplevel-state.Γ s)
      (check-args-against-params (just (location-data (fnᵢ , first-position))) pi-v psᵢ as) ≫span
    spanMr (maybe-if op ≫maybe
            public-import-params-ok psₒ (qualif-args (toplevel-state.Γ s) as))

-- the call to ctxt-update-symbol-occurrences is for cedille-find functionality
process-cmds (mk-toplevel-state include-path files is Γ) (c :: cs) need-to-check =
  process-cmd (mk-toplevel-state include-path files is Γ) c need-to-check ≫=span λ s →
  process-cmds s cs need-to-check
process-cmds s [] need-to-check = set-ctxt (toplevel-state.Γ s) ≫span spanMr s

process-ctrs X Xₜ piₓ ps s csₒ b = h s csₒ b where
  h : process-t ctrs
  h s [] _ = spanMr s
  h s ((Ctr pi x T) :: cs) ff =
    h s cs ff ≫span get-ctxt λ Γ →
    spanMr (record s {Γ = ctxt-ctr-def pi x
      (subst Γ Xₜ X (hnf-ctr Γ X (qualif-type Γ T))) ps (length csₒ) (length csₒ ∸ suc (length cs)) Γ})
  h s ((Ctr pi x T) :: cs) tt =
    check-type T (just star) ≫span get-ctxt λ Γ →
    let T = hnf-ctr Γ X (qualif-type Γ T)
        neg-ret-err = ctr-positive Γ X T ≫=maybe λ neg-ret →
          let err-msg = if neg-ret then " occurs negatively in the" else " is not the return" in
          just (unqual-local X ^ err-msg ^ " type of the constructor")
        T = subst Γ Xₜ X T in
    h s cs tt ≫=span λ s →
    set-ctxt (toplevel-state.Γ s) ≫span get-ctxt λ Γ →
    check-redefined pi x (record s {Γ = Γ})
      (set-ctxt (ctxt-ctr-def pi x T ps (length csₒ) (length csₒ ∸ suc (length cs)) Γ) ≫span get-ctxt λ Γ →
       spanM-add (Var-span Γ pi x checking
         [ summary-data x (ctxt-type-def piₓ globalScope OpacTrans (unqual-local X) nothing star Γ) (abs-expand-type ps T) ] neg-ret-err) ≫span
       spanMr (record s {Γ = Γ}))

process-params s (pi , ps) need-to-check =
  set-ctxt (toplevel-state.Γ s) ≫span
  (if need-to-check then check-and-add-params else dont-check-and-add-params)
    pi ps ≫=span λ _ →
  spanM-set-params ps ≫span
  get-ctxt λ Γ → 
  spanMr (record s {Γ = ctxt-add-current-params Γ})

process-start s filename pn (File is pi1 pi2 mn ps cs pi3) need-to-check =
  λ Γ ss → progress-update pn need-to-check ≫monad
  (process-cmds s (imps-to-cmds is) need-to-check ≫=span λ s →
   process-params s (params-end-pos first-position ps , ps) need-to-check ≫=span λ s →
   process-cmds s cs need-to-check ≫=span λ s → 
   process-cwst s filename ≫=span λ s →
     spanM-add (File-span (toplevel-state.Γ s) first-position (posinfo-plus pi3 1) filename) ≫span
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

