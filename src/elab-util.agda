import cedille-options
module elab-util (options : cedille-options.options) where

open import general-util
open import cedille-types
open import syntax-util
open import type-util
open import ctxt
open import conversion
open import constants
open import instances
open import subst
open import rename
open import rewriting
open import free-vars
open import toplevel-state options {IO}
open import datatype-util
open import bohm-out

rename-validify : string → string
rename-validify = 𝕃char-to-string ∘ (h ∘ string-to-𝕃char) where
  validify-char : char → 𝕃 char
  validify-char '/' = [ '-' ]
  validify-char '.' = [ '-' ]
  validify-char c with
    (c =char 'a')  ||
    (c =char 'z')  ||
    (c =char 'A')  ||
    (c =char 'Z')  ||
    (c =char '\'') ||
    (c =char '-')  ||
    (c =char '_')  ||
    is-digit c     ||
    (c =char qual-local-chr)  ||
    (('a' <char c) && (c <char 'z')) ||
    (('A' <char c) && (c <char 'Z'))
  ...| tt = [ c ]
  ...| ff = 'Z' :: string-to-𝕃char (ℕ-to-string (toNat c)) ++ [ 'Z' ]
  h : 𝕃 char → 𝕃 char
  h [] = []
  h (c :: cs) = validify-char c ++ h cs

-- Returns a fresh variable name by adding primes and replacing invalid characters
fresh-var' : string → (string → 𝔹) → string
fresh-var' x f = fresh-h f (rename-validify x)

rename-new_from_for_ : ∀ {X : Set} → var → ctxt → (var → X) → X
rename-new ignored-var from Γ for f = f $ fresh-var' "x" (ctxt-binds-var Γ)
rename-new x from Γ for f = f $ fresh-var' x (ctxt-binds-var Γ)

rename_from_for_ : ∀ {X : Set} → var → ctxt → (var → X) → X
rename ignored-var from Γ for f = f ignored-var
rename x from Γ for f = f $ fresh-var' x (ctxt-binds-var Γ)

get-renaming : renamectxt → var → var → var × renamectxt
get-renaming ρₓ xₒ x = let x' = fresh-var' x (renamectxt-in-field ρₓ) in x' , renamectxt-insert ρₓ xₒ x'

rename_-_from_for_ : ∀ {X : Set} → var → var → renamectxt → (var → renamectxt → X) → X
rename xₒ - ignored-var from ρₓ for f = f ignored-var ρₓ
rename xₒ - x from ρₓ for f = uncurry f $ get-renaming ρₓ xₒ x

rename_-_lookup_for_ : ∀ {X : Set} → var → var → renamectxt → (var → renamectxt → X) → X
rename xₒ - x lookup ρₓ for f with renamectxt-lookup ρₓ xₒ
...| nothing = rename xₒ - x from ρₓ for f
...| just x' = f x' ρₓ

rename_from_and_for_ : ∀ {X : Set} → var → ctxt → renamectxt → (var → ctxt → renamectxt → X) → X
rename ignored-var from Γ and ρ for f = f ignored-var Γ ρ
rename x from Γ and ρ for f =
  let x' = fresh-var' x (λ x → ctxt-binds-var Γ x || renamectxt-in-field ρ x) in
  f x' (ctxt-var-decl x' Γ) (renamectxt-insert ρ x x')

module reindexing (Γ : ctxt) (D I mn : var) (isₒ : indices) (psₜ : params) where

  rnm : Set
  rnm = qualif × stringset
  
  rnm-insert : rnm → var → var → rnm
  rnm-insert (q , s) xₒ xₙ = trie-insert q xₒ (xₙ , []) , stringset-insert s xₙ

  rnm-add : rnm → var → var → args → rnm
  rnm-add (q , s) xₒ xₙ as = trie-insert q xₒ (xₙ , as) , stringset-insert s xₙ
  
  rnm-binds : rnm → var → 𝔹
  rnm-binds (q , s) x = trie-contains q x || trie-contains s x

  reindex-fresh-var : rnm → trie indices → var → var
  reindex-fresh-var ρₓ is ignored-var = ignored-var
  reindex-fresh-var ρₓ is x =
    fresh-h (λ x' → ctxt-binds-var Γ x' || trie-contains is x' || rnm-binds ρₓ x') x

  rename-indices' : rnm → trie indices → indices
  rename-indices' ρₓ is = foldr {B = renamectxt → rnm → indices}
    (λ {(Index x atk) f r ρₓ →
       let x' = reindex-fresh-var ρₓ is x in
       Index x' (substh Γ r empty-trie -tk atk) :: f (renamectxt-insert r x x') (rnm-insert ρₓ x x')})
    (λ r ρₓ → []) isₒ empty-renamectxt ρₓ
  
  reindex-t : Set → Set
  reindex-t X = rnm → trie indices → X → X
  
  {-# TERMINATING #-}
  reindex : ∀ {ed} → reindex-t ⟦ ed ⟧

  rc-is : rnm → indices → rnm
  rc-is = foldr λ {(Index x atk) ρₓ → rnm-insert ρₓ x x}

  is-index-var : maybe tpkd → 𝔹
  is-index-var (just (Tkt (TpVar x))) = x =string I
  is-index-var _ = ff
  
  reindex {TERM} ρₓ is (AppEr t (Var x)) with trie-lookup is x
  ...| nothing = AppEr (reindex ρₓ is t) $ reindex ρₓ is $ Var x
  ...| just is' = indices-to-apps is' $ reindex ρₓ is t
  reindex {TERM} ρₓ is (App t t') =
    App (reindex ρₓ is t) (reindex ρₓ is t')
  reindex {TERM} ρₓ is (AppE t tT) =
    AppE (reindex ρₓ is t) (reindex ρₓ is -tT tT)
  reindex {TERM} ρₓ is (Beta t t') =
    Beta (reindex ρₓ is t) (reindex ρₓ is t')
  reindex {TERM} ρₓ is (Delta b? T t) =
    Delta (b? >>=c λ t₁ t₂ → just (reindex ρₓ is t₁ , reindex ρₓ is t₂))
          (reindex ρₓ is T) (reindex ρₓ is t)
  reindex {TERM} ρₓ is (Hole pi) =
    Hole pi
  reindex {TERM} ρₓ is (IotaPair t₁ t₂ x Tₓ) =
    let x' = reindex-fresh-var ρₓ is x in
    IotaPair (reindex ρₓ is t₁) (reindex ρₓ is t₂) x'
      (reindex (rnm-insert ρₓ x x') is Tₓ)
  reindex {TERM} ρₓ is (IotaProj t n) =
    IotaProj (reindex ρₓ is t) n
  reindex {TERM} ρₓ is (Lam me x tk? t) with is-index-var tk?
  ...| ff = let x' = reindex-fresh-var ρₓ is x in
    Lam me x' (reindex ρₓ is -tk_ <$> tk?) (reindex (rnm-insert ρₓ x x') is t)
  ...| tt with rename-indices' ρₓ is
  ...| isₙ = indices-to-lams isₙ $ reindex (rc-is ρₓ isₙ) (trie-insert is x isₙ) t
  reindex {TERM} ρₓ is (LetTm me x T? t t') =
    let x' = reindex-fresh-var ρₓ is x in
    LetTm me x' (reindex ρₓ is <$> T?) (reindex ρₓ is t) (reindex (rnm-insert ρₓ x x') is t')
  reindex {TERM} ρₓ is (LetTp x k T t) =
    let x' = reindex-fresh-var ρₓ is x in
    LetTp x' (reindex ρₓ is k) (reindex ρₓ is T) (reindex (rnm-insert ρₓ x x') is t)
  reindex {TERM} ρₓ is (Phi t₌ t₁ t₂) =
    Phi (reindex ρₓ is t₌) (reindex ρₓ is t₁) (reindex ρₓ is t₂)
  reindex {TERM} ρₓ is (Rho t₌ x Tₓ t) =
    let x' = reindex-fresh-var ρₓ is x in
    Rho (reindex ρₓ is t) x' (reindex (rnm-insert ρₓ x x') is Tₓ) (reindex ρₓ is t)
  reindex {TERM} ρₓ is (VarSigma t) =
    VarSigma (reindex ρₓ is t)
  reindex {TERM} ρₓ is (Var x) =
    maybe-else' (trie-lookup (fst ρₓ) x) (Var x) (uncurry (apps-term ∘ Var))
  reindex {TERM} ρₓ is (Mu μ t Tₘ? f~ cs) = Var "template-mu-not-allowed"
  reindex {TERM} ρₓ is (Sigma μ t Tₘ? f~ cs) = Var "template-sigma-not-allowed"
  
  reindex {TYPE} ρₓ is (TpAbs me x atk T) with is-index-var (just atk)
  ...| ff = let x' = reindex-fresh-var ρₓ is x in
    TpAbs me x' (reindex ρₓ is -tk atk) (reindex (rnm-insert ρₓ x x') is T)
  ...| tt = let isₙ = rename-indices' ρₓ is in
    indices-to-alls isₙ $ reindex (rc-is ρₓ isₙ) (trie-insert is x isₙ) T
  reindex {TYPE} ρₓ is (TpEq t₁ t₂) =
    TpEq (reindex ρₓ is t₁) (reindex ρₓ is t₂)
  reindex {TYPE} ρₓ is (TpIota x T T') =
    let x' = reindex-fresh-var ρₓ is x in
    TpIota x' (reindex ρₓ is T) (reindex (rnm-insert ρₓ x x') is T')
  reindex {TYPE} ρₓ is (TpAppTm T (Var x)) with trie-lookup is x
  ...| nothing = TpAppTm (reindex ρₓ is T) $ reindex ρₓ is $ Var x
  ...| just is' = indices-to-tpapps is' $ reindex ρₓ is T
  reindex {TYPE} ρₓ is (TpApp T tT) =
    TpApp (reindex ρₓ is T) (reindex ρₓ is -tT tT)
  reindex {TYPE} ρₓ is (TpHole pi) =
    TpHole pi
  reindex {TYPE} ρₓ is (TpLam x atk T) with is-index-var (just atk)
  ...| ff = let x' = reindex-fresh-var ρₓ is x in
    TpLam x' (reindex ρₓ is -tk atk) (reindex (rnm-insert ρₓ x x') is T)
  ...| tt = let isₙ = rename-indices' ρₓ is in
    indices-to-tplams isₙ $ reindex (rc-is ρₓ isₙ) (trie-insert is x isₙ) T
  reindex {TYPE} ρₓ is (TpVar x) =
    maybe-else' (trie-lookup (fst ρₓ) x) (TpVar x) (uncurry (apps-type ∘ TpVar))
  
  reindex {KIND} ρₓ is (KdAbs x atk k) with is-index-var (just atk)
  ...| ff = let x' = reindex-fresh-var ρₓ is x in
    KdAbs x' (reindex ρₓ is -tk atk) (reindex (rnm-insert ρₓ x x') is k)
  ...| tt = let isₙ = rename-indices' ρₓ is in
    indices-to-kind isₙ $ reindex (rc-is ρₓ isₙ) (trie-insert is x isₙ) k
  reindex {KIND} ρₓ is (KdHole pi) =
    KdHole pi
  reindex {KIND} ρₓ is KdStar =
    KdStar

  reindex-cmd : rnm → trie indices → cmd → cmd × rnm
  reindex-cmd ρₓ is (CmdImport (Import p? fp mnᵢ q? as)) =
    CmdImport (Import p? fp mnᵢ q? (reindex ρₓ is -arg_ <$> as)) , ρₓ
  reindex-cmd ρₓ is (CmdDefTerm x t) =
    let x' = D ^ "/" ^ x in
    CmdDefTerm x' (lam-expand-term psₜ $ reindex ρₓ is t) ,
    rnm-add ρₓ (mn # x) (ctxt.mn Γ # x') (params-to-args psₜ)
  reindex-cmd ρₓ is (CmdDefType x k T) =
    let x' = D ^ "/" ^ x in
    CmdDefType x' (abs-expand-kind psₜ $ reindex ρₓ is k)
                  (lam-expand-type psₜ $ reindex ρₓ is T) ,
    rnm-add ρₓ (mn # x) (ctxt.mn Γ # x') (params-to-args psₜ)
  reindex-cmd ρₓ is (CmdDefKind x ps k) =
    CmdDefKind x ps k , ρₓ
  reindex-cmd ρₓ is (CmdDefData es x ps k cs) =
    CmdDefData es x ps k cs , ρₓ
  
  reindex-cmds : cmds → cmds
  reindex-cmds cs =
    foldr {B = rnm → cmds}
      (λ c rec ρₓ → elim reindex-cmd ρₓ empty-trie c for λ c ρₓ → c :: rec ρₓ)
      (λ ρₓ → []) cs (empty-trie , empty-stringset)

{- we have to erase params to work around a situation like

data MyData (x : {β ≃ β}) : ★ =
| MyCtr : MyData.

erased-problem : ∀ x : {β ≃ β}. MyData x ➔ MyData β{λ x. x} =
  Λ x. λ d. μ' d { MyCtr ➔ MyCtr β{λ x. x} }.
  ^----------------------------------------^
... because the indicated term would elaborate to something like

Λ x. λ d. FixInd x ·MyData d ...
^-^              ^

and "x" is bound by an erased lambda, but is an unerased arg to FixInd!
(similar situations arise with fix-in/fix-out and with module parameters)
-}

reindex-file : ctxt → (D I modname : var) → indices → params → cmds → cmds
reindex-file Γ D I mn is ps cs =
  let ps' = params-set-erased Erased (ctxt.ps Γ ++ ps)
      open reindexing (add-params-to-ctxt ps' Γ) D I mn is ps' in
  reindex-cmds cs

mendler-elab-mu : ctxt → datatype-info → var → term → type → cases → term
mendler-elab-mu-pure : ctxt → datatype-info → var → term → cases → term

mendler-elab-sigma : ctxt → datatype-info → maybe term → term → type → cases → term
mendler-elab-sigma-pure : ctxt → datatype-info → maybe term → term → cases → term

-- Maps over expression, elaborating all mu-terms
{-# TERMINATING #-}
choose-mu : ∀ {ed} → ctxt → renamectxt → ⟦ ed ⟧ → ⟦ ed ⟧
choose-mu {TERM} Γ ρ (App tm tm') =
  App (choose-mu Γ ρ tm) (choose-mu Γ ρ tm')
choose-mu {TERM} Γ ρ (AppE tm tT) =
  AppE (choose-mu Γ ρ tm) (choose-mu Γ ρ -tT tT)
choose-mu {TERM} Γ ρ (Beta tm tm') =
  Beta (choose-mu Γ ρ tm) (choose-mu Γ ρ tm')
choose-mu {TERM} Γ ρ (Delta b? tp tm) =
  maybe-else' (b? >>=c λ t₁ t₂ →
               make-contradiction
                 (hnf Γ unfold-all (choose-mu Γ ρ t₁))
                 (hnf Γ unfold-all (choose-mu Γ ρ t₂)))
    (Delta nothing (choose-mu Γ ρ tp) (choose-mu Γ ρ tm)) λ f →
  rename "x" from Γ and ρ for λ x' _ _ →
  Delta (just (tt-term , ff-term)) (choose-mu Γ ρ tp)
    (Rho (choose-mu Γ ρ tm) x' (TpEq (App f (Var x')) ff-term) (Beta ff-term id-term))
choose-mu {TERM} Γ ρ (Hole pi) =
  Hole pi
choose-mu {TERM} Γ ρ (IotaPair tm₁ tm₂ x Tₓ) =
  rename x from Γ and ρ for λ x' Γ' ρ' →
  IotaPair (choose-mu Γ ρ tm₁) (choose-mu Γ ρ tm₂) x' (choose-mu Γ' ρ' Tₓ)
choose-mu {TERM} Γ ρ (IotaProj tm n) =
  IotaProj (choose-mu Γ ρ tm) n
choose-mu {TERM} Γ ρ (Lam e x tk? tm) =
  rename x from Γ and ρ for λ x' Γ' ρ' →
  Lam e x' (choose-mu Γ ρ -tk_ <$> tk?) (choose-mu Γ' ρ' tm)
choose-mu {TERM} Γ ρ (LetTm e x tp? tm tm') =
  rename x from Γ and ρ for λ x' Γ' ρ' →
  LetTm e x' (choose-mu Γ ρ <$> tp?) (choose-mu Γ ρ tm) (choose-mu Γ' ρ' tm')
choose-mu {TERM} Γ ρ (LetTp x k T t) =
  rename x from Γ and ρ for λ x' Γ' ρ' →
  LetTp x' (choose-mu Γ ρ k) (choose-mu Γ ρ T) (choose-mu Γ' ρ' t)
choose-mu {TERM} Γ ρ (Phi tm₌ tm₁ tm₂) =
  Phi (choose-mu Γ ρ tm₌) (choose-mu Γ ρ tm₁) (choose-mu Γ ρ tm₂)
choose-mu {TERM} Γ ρ (Rho tm₌ x Tₓ tm) =
  rename x from Γ and ρ for λ x' Γ' ρ' →
  Rho (choose-mu Γ ρ tm₌) x' (choose-mu Γ' ρ' Tₓ) (choose-mu Γ ρ tm)
choose-mu {TERM} Γ ρ (VarSigma tm) =
  VarSigma (choose-mu Γ ρ tm)
choose-mu {TERM} Γ ρ (Mu x t tp? t~ ms) =
  choose-mu Γ ρ
    (maybe-else' tp?
      (mendler-elab-mu-pure Γ t~ x t ms)
      (λ tp → mendler-elab-mu Γ t~ x t tp ms))
choose-mu {TERM} Γ ρ (Sigma mt t tp? t~ ms) =
  choose-mu Γ ρ
    (maybe-else' tp?
      (mendler-elab-sigma-pure Γ t~ mt t ms)
      (λ tp → mendler-elab-sigma Γ t~ mt t tp ms))
choose-mu {TERM} Γ ρ (Var x) =
  Var (renamectxt-rep ρ x)
choose-mu {TYPE} Γ ρ (TpAbs e x tk tp) =
  rename x from Γ and ρ for λ x' Γ' ρ' →
  TpAbs e x' (choose-mu Γ ρ -tk tk) (choose-mu Γ' ρ' tp)
choose-mu {TYPE} Γ ρ (TpIota x tp₁ tp₂) =
  rename x from Γ and ρ for λ x' Γ' ρ' →
  TpIota x' (choose-mu Γ ρ tp₁) (choose-mu Γ' ρ' tp₂)
choose-mu {TYPE} Γ ρ (TpApp tp tT) =
  TpApp (choose-mu Γ ρ tp) (choose-mu Γ ρ -tT tT)
choose-mu {TYPE} Γ ρ (TpEq tmₗ tmᵣ) =
  TpEq (choose-mu Γ ρ tmₗ) (choose-mu Γ ρ tmᵣ)
choose-mu {TYPE} Γ ρ (TpHole pi) =
  TpHole pi
choose-mu {TYPE} Γ ρ (TpLam x tk tp) =
  rename x from Γ and ρ for λ x' Γ' ρ' →
  TpLam x' (choose-mu Γ ρ -tk tk) (choose-mu Γ' ρ' tp)
choose-mu {TYPE} Γ ρ (TpVar x) =
  TpVar (renamectxt-rep ρ x)
choose-mu {KIND} Γ ρ (KdAbs x tk kd) =
  rename x from Γ and ρ for λ x' Γ' ρ' →
  KdAbs x' (choose-mu Γ ρ -tk tk) (choose-mu Γ' ρ' kd)
choose-mu {KIND} Γ ρ (KdHole pi) =
  KdHole pi
choose-mu {KIND} Γ ρ KdStar =
  KdStar


-- Adds all Dₓ's encoding defs to the ctxt
ctxt-open-encoding-defs : var → ctxt → maybe ctxt
ctxt-open-encoding-defs Dₓ Γ =
  trie-lookup (ctxt.μ~ Γ) Dₓ >>=r λ xs →
  let tmd = λ t → term-def nothing opacity-open (just t) (TpHole pi-gen)
      tpd = λ T → type-def nothing opacity-open (just T) (KdHole pi-gen) in
  record Γ {
    i = foldr (uncurry λ x tT i →
          trie-insert i x
            (either-else' tT
              (tmd ∘ hnf (record Γ {i = i}) unfold-head)
              (tpd ∘ hnf (record Γ {i = i}) unfold-head-elab) ,
             missing-location)) (ctxt.i Γ) xs
  }

ctxt-open-all-encoding-defs : ctxt → ctxt
ctxt-open-all-encoding-defs Γ =
  foldr (λ Dₓ Γ → maybe-else Γ id $ ctxt-open-encoding-defs Dₓ Γ)
    Γ (trie-strings (ctxt.μ~ Γ))


mk-ctr-fmap-t : Set → Set
mk-ctr-fmap-t X = ctxt → (var × type × term) → X
{-# TERMINATING #-}
mk-ctr-fmap-η+ : mk-ctr-fmap-t (term → type → term)
mk-ctr-fmap-η- : mk-ctr-fmap-t (term → type → term)
mk-ctr-fmap-η? : 𝔹 → mk-ctr-fmap-t (term → type → term)
mk-ctr-fmap-η= : 𝔹 → mk-ctr-fmap-t (term → type → term)
mk-ctr-fmapₖ-η+ : mk-ctr-fmap-t (type → kind → type)
mk-ctr-fmapₖ-η- : mk-ctr-fmap-t (type → kind → type)
mk-ctr-fmapₖ-η? : 𝔹 → mk-ctr-fmap-t (type → kind → type)

-- TODO: Join fmap+ and fmap- into one function, to handle this for both strictly positive and strictly negative parameter occurrences in other datatypes
mk-ctr-fmap-η= f Γ x @ (Aₓ , Bₓ , castₓ) body T with decompose-ctr-type Γ T
...| TpVar x'' , as , rs =
  maybe-else' (data-lookup (add-params-to-ctxt as Γ) x'' rs) ((if f then mk-ctr-fmap-η+ else mk-ctr-fmap-η-) Γ x body T) λ where
    d @ (mk-data-info X _ asₚ asᵢ ps kᵢ k cs csₚₛ eds gds) →
      params-to-lams (if f then as else (substh-params Γ empty-renamectxt (trie-single Aₓ (, Bₓ)) as)) $
      let Γ' = add-params-to-ctxt as Γ
          recₓ = fresh-var Γ' "fmap"
          Γ' = ctxt-var-decl recₓ Γ'
          is = kind-to-indices Γ k
          uₓ = fresh-var (add-indices-to-ctxt is Γ') "u"
          vₓ = fresh-var (add-indices-to-ctxt is Γ') "v"
          Γ'' = ctxt-var-decl vₓ $ ctxt-var-decl uₓ $ add-indices-to-ctxt is Γ' in
      LetTm tt uₓ nothing
        (Mu recₓ
          (foldl
            (λ {(Param me x'' (Tkt T)) body →
                  (if me then AppEr body else App body) $
                     mk-ctr-fmap-η? (~ f) Γ' x (Var x'') T;
                (Param _ x'' (Tkk k)) body →
                  AppTp body $ mk-ctr-fmapₖ-η? (~ f) Γ' x (TpVar x'') k})
            body as)
          (just (indices-to-tplams is $
            TpLam uₓ (Tkt $ indices-to-tpapps is $ recompose-tpapps (args-to-tmtps asₚ) (TpVar X)) $
              TpIota vₓ (subst Γ'' Bₓ Aₓ (recompose-tpapps (args-to-tmtps asₚ) (TpVar X)))
                (TpEq (Var vₓ) (Var uₓ)))) d $
          flip map (map-snd (rename-var Γ'' (mu-Type/ recₓ) X) <$> inst-ctrs Γ'' ps asₚ cs) $ uncurry λ cₓ T → case decompose-ctr-type Γ T of λ where
            (Tₕ , as , rs) →
              Case cₓ (map (λ {(Param me x tk) → CaseArg me x (just tk)}) as)
                (let Xₚₛ = recompose-tpapps (args-to-tmtps asₚ) (TpVar X)
                     cg = mu-Type/ recₓ , Xₚₛ ,
                          (indices-to-lams is $ Lam ff vₓ (just (Tkt (indices-to-tpapps is (TpVar (mu-Type/ recₓ))))) (Phi (IotaProj (App (indices-to-apps is (Var recₓ)) (Var vₓ)) ι2) (IotaProj (App (indices-to-apps is (Var recₓ)) (Var vₓ)) ι1) (Var vₓ)))
                     t = foldl
                           (λ {(Param me x'' (Tkt T)) body →
                                 (if me then AppEr body else App body) $
                                   mk-ctr-fmap-η? f Γ' x (mk-ctr-fmap-η? ff Γ' cg (Var x'') T) (subst Γ'' Xₚₛ (mu-Type/ recₓ) T);
                               (Param _ x'' (Tkk k)) body →
                                 AppTp body $ mk-ctr-fmapₖ-η? f Γ' x (mk-ctr-fmapₖ-η? ff Γ' cg (TpVar x'') k) (subst Γ'' Xₚₛ (mu-Type/ recₓ) k)})
                           (subst (add-params-to-ctxt as Γ) Bₓ Aₓ (recompose-apps asₚ (Var cₓ))) as
                     tₑ = erase t in
                 IotaPair t (Beta tₑ tₑ) vₓ (TpEq (Var vₓ) tₑ))
                rs)
        (Phi (IotaProj (Var uₓ) ι2) (IotaProj (Var uₓ) ι1) (erase (params-to-apps as body)))
--  maybe-else' (ctxt-open-encoding-defs x'' Γ) (f Γ x body T)
--    λ Γ → f Γ x body (hnf-ctr Γ (fst x) T)
...| _ = (if f then mk-ctr-fmap-η+ else mk-ctr-fmap-η-) Γ x body T

mk-ctr-fmap-η? f Γ x body T with is-free-in (fst x) T
...| tt = mk-ctr-fmap-η= f Γ x body T
...| ff = body

mk-ctr-fmapₖ-η? f Γ x body k with is-free-in (fst x) k
...| tt = (if f then mk-ctr-fmapₖ-η+ else mk-ctr-fmapₖ-η-) Γ x body k
...| ff = body

mk-ctr-fmap-η+ Γ x @ (Aₓ , Bₓ , _) body T with decompose-ctr-type Γ T
...| Tₕ , as , _ =
  params-to-lams as $
  let Γ' = add-params-to-ctxt as Γ
      tₓ' = case Tₕ of λ where
              (TpIota x'' T₁ T₂) body →
                let t₁ = mk-ctr-fmap-η+ Γ' x (IotaProj body ι1) T₁
                    t₂ = mk-ctr-fmap-η+ Γ' x (IotaProj body ι2) (subst Γ' t₁ x'' T₂) in
                IotaPair t₁ t₂ x'' T₂
              _ body → body
  in
  tₓ' $ foldl
    (λ {(Param me x'' (Tkt T)) body →
          (if me then AppEr body else App body) $
            mk-ctr-fmap-η? ff Γ' x (Var x'') T;
        (Param _ x'' (Tkk k)) body →
          AppTp body $ mk-ctr-fmapₖ-η? ff Γ' x (TpVar x'') k})
    body as

mk-ctr-fmap-η- Γ xₒ @ (Aₓ , Bₓ , castₓ) body T with decompose-ctr-type Γ T
...| TpVar x'' , as , rs =
  params-to-lams (substh-params Γ empty-renamectxt (trie-single Aₓ (, Bₓ)) as) $
  let Γ' = add-params-to-ctxt as Γ in
  if x'' =string Aₓ
    then App (recompose-apps (tmtps-to-args Erased rs) castₓ)
    else id $
  foldl (λ {(Param me x'' (Tkt T)) body →
              (if me then AppEr body else App body) $
                 mk-ctr-fmap-η? tt Γ' xₒ (Var x'') T;
            (Param me x'' (Tkk k)) body →
              AppTp body $ mk-ctr-fmapₖ-η? tt Γ' xₒ (TpVar x'') k}) body as
...| TpIota x'' T₁ T₂ , as , [] =
  let Γ' = add-params-to-ctxt as Γ
      tₒ = foldl (λ where
            (Param me x'' (Tkt T)) body →
              (if me then AppEr body else App body) $
                mk-ctr-fmap-η? tt Γ' xₒ (Var x'') T
            (Param me x'' (Tkk k)) body →
              AppTp body $ mk-ctr-fmapₖ-η? tt Γ' xₒ (TpVar x'') k
           ) body as
      t₁ = mk-ctr-fmap-η? ff Γ' xₒ (IotaProj tₒ ι1) T₁
      t₂ = mk-ctr-fmap-η? ff Γ' xₒ (IotaProj tₒ ι2) ([ Γ' - t₁ / x'' ] T₂) in
  params-to-lams (substh-params Γ empty-renamectxt (trie-single Aₓ (, Bₓ)) as) $
  IotaPair t₁ t₂ x'' (subst (ctxt-var-decl x'' Γ') Bₓ Aₓ T₂)
...| Tₕ , as , rs = body

mk-ctr-fmapₖ-η+ Γ xₒ @ (Aₓ , Bₓ , castₓ) body k =
  let is = kind-to-indices Γ k in
  indices-to-tplams is $
  let Γ' = add-indices-to-ctxt is Γ in
  foldl
    (λ {(Index x'' (Tkt T)) → flip TpAppTm $ mk-ctr-fmap-η?  ff Γ' xₒ (Var x'') T;
        (Index x'' (Tkk k)) → flip TpAppTp $ mk-ctr-fmapₖ-η? ff Γ' xₒ (TpVar x'') k})
    body is

mk-ctr-fmapₖ-η- Γ xₒ @ (Aₓ , Bₓ , castₓ) body k with kind-to-indices Γ k
...| is =
  indices-to-tplams is $
  let Γ' = add-indices-to-ctxt is Γ in
  foldl (λ {(Index x'' (Tkt T)) → flip TpAppTm $ mk-ctr-fmap-η? tt Γ' xₒ (Var x'') T;
            (Index x'' (Tkk k)) → flip TpApp $ Ttp $ mk-ctr-fmapₖ-η? tt Γ' xₒ (TpVar x'') k})
    body is


mk-def : term → term
mk-def t = Phi (Beta t id-term) t (erase t)

top-type : type
top-type = TpEq id-term id-term

-- Index telescoping parameter
pattern IdxTele Iₓ = Param tt Iₓ (Tkk KdStar) :: []
pattern EncArgIdx I = ArgTp I
pattern EncArgCast Cast = ArgTp Cast
pattern EncArgCastIn cast-in = Arg cast-in
pattern EncArgCastOut cast-out = Arg cast-out
pattern EncArgCastIs cast-is = Arg cast-is
pattern EncArgFunctor Functor = ArgTp Functor
pattern EncArgFunctorIn functor-in = Arg functor-in
pattern EncArgFunctorOut functor-out = Arg functor-out
pattern EncArgFix Fix = ArgTp Fix
pattern EncArgFixIn fix-in = Arg fix-in
pattern EncArgFixOut fix-out = Arg fix-out
pattern EncArgLambek1 lambek1 = Arg lambek1
pattern EncArgLambek2 lambek2 = Arg lambek2
pattern EncArgFixInd fix-ind = Arg fix-ind
pattern EncArgs I Cast cast-in cast-out cast-is Functor functor-in functor-out
                Fix fix-in fix-out lambek1 lambek2 fix-ind =
  EncArgIdx I ::
  EncArgCast Cast ::
  EncArgCastIn cast-in ::
  EncArgCastOut cast-out ::
  EncArgCastIs cast-is ::
  EncArgFunctor Functor ::
  EncArgFunctorIn functor-in ::
  EncArgFunctorOut functor-out ::
  EncArgFix Fix ::
  EncArgFixIn fix-in ::
  EncArgFixOut fix-out ::
  EncArgLambek1 lambek1 ::
  EncArgLambek2 lambek2 ::
  EncArgFixInd fix-ind :: []

pattern EncImp fp I Cast cast-in cast-out cast-is Functor functor-in functor-out
               Fix fix-in fix-out lambek1 lambek2 fix-ind =
  CmdImport (Import _ fp _ _ (EncArgs
      I Cast cast-in cast-out cast-is Functor functor-in functor-out
      Fix fix-in fix-out lambek1 lambek2 fix-ind))

encode-datatype : ctxt → encoding-defs → datatype → encoding-defs
encode-datatype Γ eds @ (mk-enc-defs ecs _
                               Cast cast-in cast-out cast-is
                               Functor functor-in functor-out
                               Fix fix-in fix-out
                               lambek1 lambek2 fix-ind)
                  (Data Dₓ' ps is cs) =
  record eds {gcs = [: TypeF-cmd ⌟ IndF-cmd ⌟ fmap-cmd ⌟
                       D-cmd ⌟ Is-cmd ⌟ is-cmd ⌟ to-cmd ⌟
                       map ctr-cmd cs~ :] }
  where

  Γₚₛ = ctxt.ps Γ
  psₜ = params-set-erased Erased (Γₚₛ ++ ps)

  app-ps = params-to-apps psₜ ∘ Var
  tpapp-ps = params-to-tpapps psₜ ∘ TpVar

--  Cast = tpapp-ps Castₓ
--  cast-in = app-ps cast-inₓ
--  cast-out = app-ps cast-outₓ
--  cast-is = app-ps cast-isₓ
--  Functor = tpapp-ps Functorₓ
--  functor-in = app-ps functor-inₓ
--  functor-out = app-ps functor-outₓ
--  Fix = tpapp-ps Fixₓ
--  fix-in = app-ps fix-inₓ
--  fix-out = app-ps fix-outₓ
--  lambek1 = app-ps lambek1ₓ
--  lambek2 = app-ps lambek2ₓ
--  fix-ind = app-ps fix-indₓ

  mn = ctxt.mn Γ

  Γ' = add-params-to-ctxt psₜ Γ

  Dₓ = mn # Dₓ'
  cs~ = map-snd (subst Γ' (params-to-tpapps psₜ (TpVar Dₓ)) Dₓ) <$> cs
  cs' = map-snd (rename-var Γ' Dₓ Dₓ') <$> cs

  topᵢ = indices-to-kind is $ KdAbs ignored-var (Tkt top-type) KdStar

  mk-ctr-eterm : params → ctr → term
  mk-ctr-eterm ps (Ctr x _) =
    let xs = erase-params ps in
    Beta id-term $ foldr
      mlam
      (foldl (flip App ∘ Var) (Var x) xs)
      (map fst cs)
  
  mk-ctr-etype : ctxt → ctr → var → type
  mk-ctr-etype Γ (Ctr x T) X with decompose-ctr-type (ctxt-var-decl X Γ) T
  ...| Tₕ , as , rs =
    params-to-alls as $
    let rs' = if length rs =ℕ length psₜ + length is then drop (length psₜ) rs else rs in
    TpAppTm (recompose-tpapps rs' $ TpVar X) $ mk-ctr-eterm as (Ctr x T)
  

  {-
  for the datatype
    data Dₓ (p₁ : P₁) (p₂ : P₂)... : Π i₁ : I₁. Π i₂ : I₂. ... ★ =
      | c₁ : Π/∀ a₁ : A₁. Π/∀ a₂ : A₂. ... (Dₓ r₁ r₂...)
      | c₂ : ... .
  produce the functor type
  ∀ X : Π i₁ : I₁. Π i₂ : I₂. ... Π _ : Top. ★.
    (Π/∀ a₁ : A₁. Π/∀ a₂ : A₂. ... (X r₁ r₂ β<λ x. x>{λ c₁. λ c₂. ... |c₁ a₁ a₂...|})) →
     ... →
    X i₁ i₂... ιₓ
  -}
  mk-ftype2 : ctxt → (asᵢ : 𝕃 tmtp) → (ιₓ : var) → ctrs → type
  mk-ftype2 Γ asᵢ ιₓ cs =
    let Γ = ctxt-var-decl ιₓ Γ in
    rename "X" from Γ for λ X →
    TpAbs tt X (Tkk topᵢ) $
    foldr
      (λ c → TpAbs ff ignored-var $ Tkt $ mk-ctr-etype Γ c X)
      (TpAppTm (recompose-tpapps asᵢ $ TpVar X) $ Var ιₓ)
      cs

  mk-ctr-fterm : ctxt → ctr → ctrs → (as : params) → (rs : 𝕃 tmtp) → term
  mk-ctr-fterm Γ' (Ctr x' T) cs as rs =
    let Γ' = add-params-to-ctxt as Γ' in
    rename "X" from Γ' for λ Xₓ →
    rename "x" from Γ' for λ xₓ →
    let tkₓ = just (Tkk (indices-to-kind is (KdAbs ignored-var (Tkt top-type) KdStar)))
        fₜ = λ x T → Lam ff x (just (Tkt (mk-ctr-etype (ctxt-var-decl Xₓ Γ') (Ctr x T) Xₓ)))
        t = Lam tt Xₓ tkₓ (foldr (uncurry fₜ) (params-to-apps as (Var x')) cs) in
    IotaPair (Beta id-term (erase t)) t xₓ (mk-ftype2 (ctxt-var-decl xₓ Γ') rs xₓ cs)

  mk-ctr-ftype : ctxt → ctr → ctrs → var → type
  mk-ctr-ftype Γ (Ctr x T) cs X with decompose-ctr-type (ctxt-var-decl X Γ) T
  ...| Tₕ , as , rs =
    params-to-alls as $
    TpAppTm (recompose-tpapps rs $ TpVar X) $ mk-ctr-fterm (ctxt-var-decl X Γ) (Ctr x T) cs as rs


  Is/D = tpapp-ps (data-Is/ Dₓ)
  is/D = app-ps (data-is/ Dₓ)
  to/D = app-ps (data-to/ Dₓ)
  TypeF/D = tpapp-ps (data-TypeF/ Dₓ)
  IndF/D = tpapp-ps (data-IndF/ Dₓ)
  fmap/D = app-ps (data-fmap/ Dₓ)
  D = tpapp-ps Dₓ
  kᵢ = indices-to-kind is KdStar
  tkᵢ = Tkk kᵢ
  jtkᵢ = just tkᵢ

  decl-Γ : ctxt → 𝕃 var → ctxt
  decl-Γ = foldr ctxt-var-decl


  {-
  λ p₁ : P₁. λ p₂ : P₂. ...
    λ Dₓ : Π i₁ : I₁. Π i₂ : I₂. ... ★.
      λ i₁ : I₁. λ i₂ : I₂. ...
        ι ιₓ : Top. mk-ftype2 (ctxt-var-decl ιₓ Γ') ιₓ cs.
    -}
  TypeF-cmd = CmdDefType (data-TypeF/ Dₓ')
                (params-to-kind psₜ $ KdAbs ignored-var tkᵢ kᵢ) $
    let Γ' = add-indices-to-ctxt is Γ' in
    rename "x" from Γ' for λ ιₓ →
    params-to-tplams psₜ $
      TpLam Dₓ' (Tkk $ indices-to-kind is KdStar) $
        indices-to-tplams is $
          TpIota ιₓ top-type $ mk-ftype2 (ctxt-var-decl ιₓ Γ') (indices-to-tmtps is) ιₓ cs'
  
  fmap-cmd = CmdDefTerm (data-fmap/ Dₓ') $
    let Γ' = add-indices-to-ctxt is Γ' in
    rename "A" from Γ' for λ Aₓ →
    rename "B" from Γ' for λ Bₓ →
    rename "c" from Γ' for λ cₓ →
    rename "x" from Γ' for λ xₓ →
    rename "X" from Γ' for λ Xₓ →
    params-to-lams psₜ $
    let cs-a = map-snd (rename-var Γ' Dₓ Aₓ) <$> cs
        cs-b = map-snd (rename-var Γ' Dₓ Bₓ) <$> cs in
    AppEr (AppTp functor-in TypeF/D) $
    Lam tt Aₓ jtkᵢ $
    Lam tt Bₓ jtkᵢ $
    Lam tt cₓ (just (Tkt (TpAppTp (TpAppTp Cast (TpVar Aₓ)) (TpVar Bₓ)))) $
    AppEr (AppEr (AppTp (AppTp cast-in (TpAppTp TypeF/D (TpVar Aₓ)))
                                       (TpAppTp TypeF/D (TpVar Bₓ)))
      (indices-to-lams is $
       Lam ff xₓ (just (Tkt (indices-to-tpapps is (TpAppTp TypeF/D (TpVar Aₓ))))) $
       IotaPair (IotaProj (Var xₓ) ι1)
         (Lam tt Xₓ (just (Tkk topᵢ)) $
          flip (foldr $ uncurry λ x T → Lam ff x (just (Tkt
                 (mk-ctr-etype (decl-Γ Γ' [: Aₓ ⌟ Bₓ ⌟ cₓ ⌟ xₓ ⌟ Xₓ :]) (x , T) Xₓ)))) cs-b $
          foldl
            (flip App ∘ uncurry
              (λ bodyₓ T →
                mk-ctr-fmap-η?
                  tt
                  (decl-Γ Γ' [: Aₓ ⌟ Bₓ ⌟ cₓ ⌟ xₓ ⌟ Xₓ :])
                  (Aₓ , TpVar Bₓ , AppEr (AppTp (AppTp cast-out (TpVar Aₓ)) (TpVar Bₓ)) (Var cₓ))
                  (Var bodyₓ)
                  (hnf-ctr (decl-Γ Γ' [: Aₓ ⌟ Bₓ ⌟ cₓ ⌟ xₓ ⌟ Xₓ :]) Aₓ T)))
            (AppTp (IotaProj (Var xₓ) ι2) (TpVar Xₓ)) cs-a)
         xₓ (mk-ftype2 (decl-Γ Γ' [: Aₓ ⌟ Bₓ ⌟ cₓ ⌟ xₓ :]) (indices-to-tmtps is) xₓ cs-b)))
      (Beta id-term id-term)

  IndF-cmd = CmdDefTerm (data-IndF/ Dₓ') $
    params-to-lams psₜ $
    Lam tt Dₓ' jtkᵢ $
    indices-to-lams is $
    let Γ' = add-indices-to-ctxt is Γ' in
    rename "x" from Γ' for λ xₓ →
    rename "y" from Γ' for λ yₓ →
    rename "e" from Γ' for λ eₓ →
    rename "X" from Γ' for λ Xₓ →
    let T = indices-to-tpapps is (TpAppTp TypeF/D (TpVar Dₓ'))
        Γ' = ctxt-var-decl xₓ (ctxt-var-decl Xₓ Γ') in
    Lam ff xₓ (just $ Tkt T) $
    Lam tt Xₓ (just $ Tkk $ indices-to-kind is $ KdAbs ignored-var (Tkt T) KdStar) $
    flip (foldr λ c → Lam ff (fst c) (just (Tkt (mk-ctr-ftype Γ' c cs' Xₓ)))) cs' $
    flip AppEr (Beta (Var xₓ) id-term) $
    flip AppEr (Var xₓ) $
    let Γ' = decl-Γ Γ' [: xₓ ⌟ yₓ ⌟ eₓ ⌟ Xₓ :] in
    flip (foldl $ uncurry λ x' T' →
      case decompose-ctr-type Γ' T' of λ where
        (Tₕ , as , rs) →
          flip App $
          params-to-lams as $
          Lam tt yₓ (just (Tkt (recompose-tpapps rs (TpAppTp TypeF/D Tₕ)))) $
          Lam tt eₓ (just (Tkt (TpEq (Var yₓ) (mk-ctr-eterm as (Ctr x' T'))))) $
          params-to-apps as $
          Var x') cs' $
    AppTp (IotaProj (Var xₓ) ι2) $
    indices-to-tplams is $
    TpLam xₓ (Tkt top-type) $
    TpAbs tt yₓ (Tkt T) $
    TpAbs tt eₓ (Tkt $ TpEq (Var yₓ) (Var xₓ)) $
    TpAppTm (indices-to-tpapps is $ TpVar Xₓ) $
    Phi (Var eₓ) (Var yₓ) (Var xₓ)

  D-cmd = CmdDefType Dₓ' (params-to-kind (Γₚₛ ++ ps) kᵢ) $
    params-to-tplams (Γₚₛ ++ ps) $
    TpAppTm (TpApp Fix (Ttp TypeF/D)) fmap/D

  is-projn : ctxt → type → type → term → type
  is-projn Γ Tₘ Tₙ t =
    rename "i" from Γ for λ iₓ →
    TpIota iₓ
      (indices-to-alls is
        (TpAbs ff ignored-var (Tkt (indices-to-tpapps is Tₘ))
          (indices-to-tpapps is Tₙ)))
      (TpEq (Var iₓ) t)

  is-proj1 = λ Γ T → is-projn Γ T D id-term
  is-proj2 = λ Γ T → is-projn Γ T (TpAppTp TypeF/D T) fix-out

  is-proj' : ctxt → var → term → term
  is-proj' Γ Xₓ mu =
    rename "c" from Γ for λ cₓ →
    rename "o" from Γ for λ oₓ →
    let t = App (AppTp mu (is-proj1 (decl-Γ Γ (cₓ :: oₓ :: [])) (TpVar Xₓ)))
              (Lam ff cₓ (just (Tkt (is-proj1 (decl-Γ Γ (cₓ :: oₓ :: [])) (TpVar Xₓ))))
                (Lam ff oₓ (just (Tkt (is-proj2 (decl-Γ Γ (cₓ :: oₓ :: [])) (TpVar Xₓ))))
                  (Var cₓ))) in
    Phi (IotaProj t ι2) (IotaProj t ι1) id-term

  Is-cmd = CmdDefType (data-Is/ Dₓ') (params-to-kind (Γₚₛ ++ ps) $ KdAbs ignored-var tkᵢ KdStar) $
    params-to-tplams (Γₚₛ ++ ps) $
    rename "X" from Γ' for λ Xₓ →
    rename "Y" from Γ' for λ Yₓ →
    TpLam Xₓ tkᵢ $
    TpAbs tt Yₓ (Tkk KdStar) $
    TpAbs ff ignored-var
      (Tkt (TpAbs ff ignored-var (Tkt (is-proj1 (decl-Γ Γ' (Xₓ :: Yₓ :: [])) (TpVar Xₓ))) $
            TpAbs ff ignored-var (Tkt (is-proj2 (decl-Γ Γ' (Xₓ :: Yₓ :: [])) (TpVar Xₓ))) $
            TpVar Yₓ))
      (TpVar Yₓ)

  is-cmd = CmdDefTerm (data-is/ Dₓ') $
    params-to-lams (Γₚₛ ++ ps) $
    rename "Y" from Γ' for λ Yₓ →
    rename "f" from Γ' for λ fₓ →
    rename "x" from Γ' for λ xₓ →
    let pair = λ t → IotaPair t (Beta (erase t) (erase t)) xₓ (TpEq (Var xₓ) (erase t)) in
    Lam tt Yₓ (just (Tkk KdStar)) $
    Lam ff fₓ (just (Tkt (TpAbs ff ignored-var (Tkt (is-proj1 (ctxt-var-decl Yₓ Γ') D)) $
                          TpAbs ff ignored-var (Tkt (is-proj2 (ctxt-var-decl Yₓ Γ') D)) $
                          TpVar Yₓ))) $
    App (App (Var fₓ) (pair (indices-to-lams is (Lam ff xₓ (just (Tkt (indices-to-tpapps is D))) (Var xₓ)))))
        (pair (AppEr (AppTp fix-out TypeF/D) fmap/D))

  to-cmd = CmdDefTerm (data-to/ Dₓ') $
    rename "Y"  from Γ' for λ Yₓ  →
    rename "mu" from Γ' for λ muₓ →
    params-to-lams (Γₚₛ ++ ps) $
    Lam tt Yₓ jtkᵢ $
    Lam tt muₓ (just (Tkt (TpApp Is/D (Ttp (TpVar Yₓ))))) $
    is-proj' (decl-Γ Γ' (Yₓ :: muₓ :: [])) Yₓ (Var muₓ)

  ctr-cmd : ctr → cmd
  ctr-cmd (Ctr x' T) with subst Γ' D Dₓ' T
  ...| T' with decompose-ctr-type Γ' T'
  ...| Tₕ , as , rs = CmdDefTerm x' $
    let Γ' = add-params-to-ctxt as Γ'
        rs = drop (length (Γₚₛ ++ ps)) rs in
    params-to-lams (Γₚₛ ++ ps) $
    params-to-lams as $
    App (recompose-apps (tmtps-to-args tt rs) $
          AppEr (AppTp fix-in TypeF/D) fmap/D) $
    mk-ctr-fterm Γ' (Ctr x' T) cs~ as rs


init-encoding : ctxt → file → datatype → string ⊎ encoding-defs
init-encoding Γ (Module mn (IdxTele Iₓ) mcs) d @ (Data Dₓ ps is cs) =
  case reverse (reindex-file Γ Dₓ Iₓ mn is ps mcs) of λ where
    (EncImp fp Iₓ'
        Cast cast-in cast-out cast-is
        Functor functor-in functor-out
        Fix fix-in fix-out
        lambek1 lambek2 fix-ind :: mcs) →
      err⊎-guard (~ conv-type Γ Iₓ' (TpVar Iₓ))
        "Index telescoping argument to last import differs from the parameter" >>
      return (encode-datatype Γ (mk-enc-defs (reverse mcs) []
                          Cast cast-in cast-out cast-is
                          Functor functor-in functor-out
                          Fix fix-in fix-out
                          lambek1 lambek2 fix-ind) d)
    (CmdImport (Import p? fn mn q? as) :: mcsᵣ) →
      inj₁ $ "Expected 14 import args, but got" ^ rope-to-string (strRun Γ (args-to-string as))
    mcsᵣ →
      inj₁ "Datatype encodings must end with import ~/.cedille/Template.ced"
  where open import to-string options
init-encoding Γ (Module mn mps mcs) (Data Dₓ ps is cs) =
  inj₁ $ "Datatype encodings must have a single module parameter of kind star, " ^
         "for index telescoping"


mendler-elab-mu-pure Γ (mk-data-info _ _ _ _ _ _ _ _ _ eds ecs) xₒ t ms =
  let fix-ind = erase (encoding-defs.fix-ind eds)
      msf = λ t → foldl
                    (λ {(Case mₓ cas mₜ asₜₚ) t →
                          App t (case-args-to-lams cas mₜ)})
                    t ms in
    rename xₒ from Γ for λ x →
    rename "y" from Γ for λ yₓ →
      let subst-msf = subst-renamectxt Γ
            (renamectxt-insert* empty-renamectxt ((xₒ , x) :: (yₓ , yₓ) :: [])) ∘ msf in
        App (App fix-ind t) (Lam ff x nothing $ Lam ff yₓ nothing $ subst-msf (Var yₓ))

mendler-elab-mu Γ (mk-data-info X Xₒ asₚ asᵢ ps kᵢ k cs csₚₛ (mk-enc-defs ecs gcs Cast cast-in cast-out cast-is Functor functor-in functor-out Fix fix-in fix-out lambek1 lambek2 fix-ind) (mk-encd-defs Is/Dₓ is/Dₓ to/Dₓ TypeF/Dₓ indF/Dₓ fmap/Dₓ)) x t Tₘ ms =
  let is = kind-to-indices Γ k
      Γᵢₛ = add-indices-to-ctxt is $ add-params-to-ctxt ps $ add-params-to-ctxt (ctxt.ps Γ) Γ
      is/X? = unless (X =string Xₒ) (Var (mu-isType/' Xₒ))
      app-ps = recompose-apps (args-set-erased tt asₚ) ∘ Var
      tpapp-ps = recompose-tpapps (args-to-tmtps asₚ) ∘ TpVar
      app-ps' = inst-term Γ ps asₚ
      tpapp-ps' = inst-type Γ ps asₚ
      fmap/D = app-ps fmap/Dₓ
      TypeF/D = tpapp-ps TypeF/Dₓ
      indF/D = app-ps indF/Dₓ
      Cast = tpapp-ps' Cast
      cast-out = app-ps' cast-out
      Functor = tpapp-ps' Functor
      functor-in = app-ps' functor-in
      functor-out = app-ps' functor-out
      Fix = tpapp-ps' Fix
      fix-in = app-ps' fix-in
      fix-out = app-ps' fix-out
      lambek1 = app-ps' lambek1
      fix-ind = app-ps' fix-ind
      Xₜₚ = recompose-tpapps (args-to-tmtps asₚ) (TpVar X)
      Xₒₜₚ = if Xₒ =string X then Xₜₚ else TpVar Xₒ
      toₓ = rename "to" from Γᵢₛ for id
      outₓ = rename "out" from Γᵢₛ for id
      to-tp = λ R → TpAppTp (TpAppTp Cast R) Xₜₚ
      out-tp = λ R → TpIota outₓ (indices-to-alls is (TpAbs ff ignored-var (Tkt (indices-to-tpapps is R)) (indices-to-tpapps is (TpAppTp TypeF/D R)))) (TpEq (Var outₓ) fix-out)
      ms' : trie term
      ms' = foldr (λ c σ → case c of λ {(Case x cas t asₜₚ) →
                let Γ' = add-caseArgs-to-ctxt cas Γᵢₛ in
                trie-insert σ x $
                rename "y" from Γ' for λ yₓ →
                rename "e" from Γ' for λ eₓ →
                rename "x" from Γ' for λ xₓ →
                case-args-to-lams cas $
                Lam tt yₓ (just (Tkt (recompose-tpapps (drop (length asₚ) asₜₚ) Xₜₚ))) $
                Lam tt eₓ (just (Tkt (TpEq (App fix-in (foldr (uncurry λ x T → Lam ff (snd (split-var x)) nothing) (foldl (λ ca t → case ca of λ {(CaseArg ff x _) → App t (Var (snd (split-var x))); _ → t}) (Var (snd (split-var x))) cas) cs)) (Var yₓ)))) $
                Rho (VarSigma (Var eₓ)) xₓ (TpAppTm (recompose-tpapps (drop (length asₚ) asₜₚ) Tₘ) (Var xₓ)) t})
              empty-trie ms
      in-fix = λ is/X? T asᵢ t → 
        (App (recompose-apps asᵢ (AppEr (AppTp fix-in TypeF/D) fmap/D)) (maybe-else' is/X? t λ is/X →
        App (recompose-apps asᵢ (AppEr (AppTp (AppTp cast-out (TpAppTp TypeF/D T)) (TpAppTp TypeF/D Xₜₚ)) (AppEr (AppTp (AppTp fmap/D T) Xₜₚ) (App (AppTp is/X (to-tp T)) (Lam ff "to" (just (Tkt (to-tp T))) $ Lam ff "out" (just (Tkt (out-tp T))) $ Var "to"))))) t))
      app-lambek = λ is/X? t T asᵢ body → AppEr (AppEr body (in-fix is/X? T asᵢ t))
        (App (recompose-apps asᵢ (AppEr (AppTp lambek1 TypeF/D) fmap/D)) (in-fix is/X? T asᵢ t)) in
  rename "x" from Γᵢₛ for λ xₓ →
  rename "y" from Γᵢₛ for λ yₓ →
  rename "y'" from ctxt-var-decl yₓ Γᵢₛ for λ y'ₓ →
  rename "z" from Γᵢₛ for λ zₓ →
  rename "e" from Γᵢₛ for λ eₓ →
  rename "X" from Γᵢₛ for λ Xₓ →
  maybe-else (Var "1") id $
  foldl {B = maybe (term → term)} -- Agda hangs without this implicit argument...?
    (uncurry λ x Tₓ rec → rec >>= λ rec → trie-lookup ms' x >>= λ t →
      just λ tₕ → App (rec tₕ) t) (just λ t → t) cs >>= λ msf →
  maybe-else (just $ Var "2") just $
  just 
    (let Rₓ = mu-Type/ x
         isRₓ = mu-isType/ x
         fcₜ = AppEr (AppTp (AppTp cast-out (TpAppTp TypeF/D (TpVar Rₓ))) (TpAppTp TypeF/D Xₜₚ))
                 (AppEr (AppTp (AppTp fmap/D (TpVar Rₓ)) Xₜₚ) (Var toₓ))
         Tₘₐ = TpLam Rₓ (Tkk (indices-to-kind is KdStar)) Tₘ
         Tₘ-fmap = rename "A" from Γᵢₛ for λ Aₓ →
                  rename "B" from Γᵢₛ for λ Bₓ →
                  rename "c" from Γᵢₛ for λ cₓ →
                  rename "d" from Γᵢₛ for λ dₓ →
                  rename "q" from Γᵢₛ for λ qₓ →
                  let Γ' = foldr ctxt-var-decl Γ (Aₓ :: Bₓ :: cₓ :: dₓ :: qₓ :: [])
                      Tₘₐ' = TpAppTm (indices-to-tpapps is (TpAppTp Tₘₐ (TpVar Aₓ))) (Var dₓ)
                      Tₘₐₕ = hnf-ctr Γ' Aₓ Tₘₐ' in
                  Lam tt Aₓ (just (Tkk k)) $
                  Lam tt Bₓ (just (Tkk k)) $
                  Lam tt cₓ (just (Tkt (TpAppTp (TpAppTp Cast (TpVar Aₓ)) (TpVar Bₓ)))) $
                  indices-to-lams is $
                  Lam tt dₓ (just (Tkt (indices-to-tpapps is Xₜₚ))) $
                  IotaPair (Lam ff qₓ (just (Tkt Tₘₐ')) (mk-ctr-fmap-η? ff Γ' (Aₓ , TpVar Bₓ , AppEr (AppTp (AppTp cast-out (TpVar Aₓ)) (TpVar Bₓ)) (Var cₓ)) (Var qₓ) Tₘₐₕ)) (Beta id-term id-term) qₓ (TpEq (Var qₓ) id-term)
    in
    App (AppEr (AppTp (App (recompose-apps (tmtps-to-args tt asᵢ) (AppEr (AppTp fix-ind TypeF/D) fmap/D)) t) Tₘₐ) Tₘ-fmap)
      (Lam tt Rₓ (just (Tkk k)) $
       Lam tt toₓ (just (Tkt (to-tp (TpVar Rₓ)))) $
       Lam tt outₓ (just (Tkt (out-tp (TpVar Rₓ)))) $
       Lam ff x (just (Tkt (indices-to-alls is (TpAbs ff xₓ (Tkt (indices-to-tpapps is (TpVar Rₓ))) (TpAppTm (indices-to-tpapps is Tₘ) (App (indices-to-apps is (AppEr (AppTp (AppTp cast-out (TpVar Rₓ)) Xₜₚ) (Var toₓ))) (Var xₓ))))))) $
       indices-to-lams is $
       Lam ff yₓ (just (Tkt (indices-to-tpapps is (TpAppTp TypeF/D (TpVar Rₓ))))) $
       LetTm tt isRₓ nothing
           (Lam tt Xₓ (just (Tkk KdStar)) $
            Lam ff xₓ (just (Tkt (TpAbs ff ignored-var (Tkt (to-tp (TpVar Rₓ)))
                                   (TpAbs ff ignored-var (Tkt (out-tp (TpVar Rₓ)))
                                     (TpVar Xₓ))))) $
            App (App (Var xₓ) (Var toₓ)) (Var outₓ))
       (app-lambek (just $ Var isRₓ) (Var yₓ) (TpVar Rₓ) (indices-to-args is) $ msf
         (AppTp (Phi (Beta (Var yₓ) id-term) (App (indices-to-apps is (AppTp indF/D (TpVar Rₓ))) (Var yₓ)) (Var yₓ))
           (indices-to-tplams is $
            TpLam yₓ (Tkt $ indices-to-tpapps is (TpAppTp TypeF/D (TpVar Rₓ))) $
            TpAbs tt y'ₓ (Tkt $ indices-to-tpapps is Xₜₚ) $
            TpAbs tt eₓ (Tkt $ TpEq (App fix-in (Var yₓ)) (Var y'ₓ)) $
             TpAppTm (indices-to-tpapps is Tₘ) (Phi (Var eₓ)
               (App (indices-to-apps is (AppEr (AppTp fix-in TypeF/D) fmap/D))
                    (App (indices-to-apps is fcₜ) (Var yₓ)))
               (Var y'ₓ)))))))


mendler-elab-sigma-pure Γ (mk-data-info _ _ _ _ _ _ _ _ _ eds ecs) x? t ms =
  let fix-out = erase (encoding-defs.fix-out eds)
      msf = λ t → foldl
                    (λ {(Case mₓ cas mₜ asₜₚ) t →
                          App t (case-args-to-lams cas mₜ)})
                    t ms in
  msf (App fix-out t)

mendler-elab-sigma Γ (mk-data-info X Xₒ asₚ asᵢ ps kᵢ k cs csₚₛ (mk-enc-defs ecs gcs Cast cast-in cast-out cast-is Functor functor-in functor-out Fix fix-in fix-out lambek1 lambek2 fix-ind) (mk-encd-defs Is/Dₓ is/Dₓ to/Dₓ TypeF/Dₓ indF/Dₓ fmap/Dₓ)) mt t Tₘ ms =
  let is = kind-to-indices Γ k
      Γᵢₛ = add-indices-to-ctxt is $ add-params-to-ctxt ps $ add-params-to-ctxt (ctxt.ps Γ) Γ
      is/X? = mt
      app-ps = recompose-apps (args-set-erased tt asₚ) ∘ Var
      tpapp-ps = recompose-tpapps (args-to-tmtps asₚ) ∘ TpVar
      app-ps' = inst-term Γ ps asₚ
      tpapp-ps' = inst-type Γ ps asₚ
      fmap/D = app-ps fmap/Dₓ
      TypeF/D = tpapp-ps TypeF/Dₓ
      to/D = recompose-apps asₚ (Var to/Dₓ)
      indF/D = app-ps indF/Dₓ
      Cast = tpapp-ps' Cast
      cast-out = app-ps' cast-out
      functor-out = app-ps' functor-out
      Fix = tpapp-ps' Fix
      fix-in = app-ps' fix-in
      fix-out = app-ps' fix-out
      lambek1 = app-ps' lambek1
      Xₜₚ = recompose-tpapps (args-to-tmtps asₚ) (TpVar X)
      Xₒₜₚ = if Xₒ =string X then Xₜₚ else TpVar Xₒ
      toₓ = rename "to" from Γᵢₛ for id
      outₓ = rename "out" from Γᵢₛ for id
      to-tp = λ R → TpAppTp (TpAppTp Cast R) Xₜₚ
      out-tp = λ R → TpIota outₓ (indices-to-alls is (TpAbs ff ignored-var (Tkt (indices-to-tpapps is R)) (indices-to-tpapps is (TpAppTp TypeF/D R)))) (TpEq (Var outₓ) fix-out)
      ms' : trie term
      ms' = foldr (λ c σ → case c of λ {(Case x cas t asₜₚ) →
                let Γ' = add-caseArgs-to-ctxt cas Γᵢₛ in
                trie-insert σ x $
                rename "y" from Γ' for λ yₓ →
                rename "e" from Γ' for λ eₓ →
                rename "x" from Γ' for λ xₓ →
                case-args-to-lams cas $
                Lam tt yₓ (just (Tkt (recompose-tpapps (drop (length asₚ) asₜₚ) Xₜₚ))) $
                Lam tt eₓ (just (Tkt (TpEq (App fix-in (foldr (uncurry λ x T → Lam ff (snd (split-var x)) nothing) (foldl (λ ca t → case ca of λ {(CaseArg ff x _) → App t (Var (snd (split-var x))); _ → t}) (Var (snd (split-var x))) cas) cs)) (Var yₓ)))) $
                Rho (VarSigma (Var eₓ)) xₓ (TpAppTm (recompose-tpapps (drop (length asₚ) asₜₚ) Tₘ) (Var xₓ)) t})
              empty-trie ms
      in-fix = λ is/X? T asᵢ t → 
        (maybe-else' (is/X? ||-maybe mt) t λ is/X → App (recompose-apps asᵢ (AppEr (AppTp (AppTp cast-out T) Xₜₚ) (App (AppTp is/X (to-tp T)) (Lam ff "to" (just (Tkt (to-tp T))) $ Lam ff "out" (just (Tkt (out-tp T))) $ Var "to")))) t)
      app-lambek = λ is/X? t T asᵢ body → AppEr (AppEr body (in-fix is/X? T asᵢ t))
        (App (recompose-apps asᵢ (AppEr (AppTp lambek1 TypeF/D) fmap/D)) (in-fix is/X? T asᵢ t)) in
  rename "x" from Γᵢₛ for λ xₓ →
  rename "y" from Γᵢₛ for λ yₓ →
  rename "y'" from ctxt-var-decl yₓ Γᵢₛ for λ y'ₓ →
  rename "z" from Γᵢₛ for λ zₓ →
  rename "e" from Γᵢₛ for λ eₓ →
  rename "X" from Γᵢₛ for λ Xₓ →
  maybe-else (Var "1") id $
  foldl {B = maybe (term → term)} -- Agda hangs without this implicit argument...?
    (uncurry λ x Tₓ rec → rec >>= λ rec → trie-lookup ms' x >>= λ t →
      just λ tₕ → App (rec tₕ) t) (just λ t → t) cs >>= λ msf →
  maybe-else (just $ Var "2") just $
  just $ 
    (app-lambek is/X? t Xₒₜₚ
             (tmtps-to-args tt asᵢ) (msf
      (let Tₛ = maybe-else' is/X? Xₜₚ λ _ → Xₒₜₚ
           fcₜ = maybe-else' is/X? id λ is/X → App $ indices-to-apps is $
             AppEr (AppTp (AppTp cast-out (TpAppTp TypeF/D Tₛ)) (TpAppTp TypeF/D Xₜₚ))
               (AppEr (AppTp (AppTp (AppEr (AppTp functor-out TypeF/D) fmap/D) Tₛ) Xₜₚ) (App (AppTp is/X (to-tp Tₛ)) (Lam ff "to" (just (Tkt (to-tp Tₛ))) $ Lam ff "out" (just (Tkt (out-tp Tₛ))) $ Var "to")))
           out = maybe-else' is/X? (AppEr (AppTp fix-out TypeF/D) fmap/D) λ is/X →
             let i = App (AppTp is/X (TpIota xₓ (indices-to-alls is (TpAbs ff ignored-var (Tkt (indices-to-tpapps is Tₛ)) (indices-to-tpapps is (TpAppTp TypeF/D Tₛ)))) (TpEq (Var xₓ) fix-out))) (Lam ff "to" (just (Tkt (to-tp Tₛ))) $ Lam ff "out" (just (Tkt (out-tp Tₛ))) $ Var "out") in
             Phi (IotaProj i ι2) (IotaProj i ι1) fix-out in
      AppTp (App (recompose-apps (tmtps-to-args tt asᵢ) (AppTp indF/D Tₛ)) (App (recompose-apps (tmtps-to-args tt asᵢ) out) t))
        (indices-to-tplams is $ TpLam yₓ (Tkt $ indices-to-tpapps is (TpAppTp TypeF/D Tₛ)) $
           TpAbs tt y'ₓ (Tkt $ indices-to-tpapps is Xₜₚ) $
           TpAbs tt eₓ (Tkt (TpEq (App fix-in (Var yₓ)) (Var y'ₓ))) $
           TpAppTm (indices-to-tpapps is Tₘ) (Phi (Var eₓ)
             (App (indices-to-apps is (AppEr (AppTp fix-in TypeF/D) fmap/D)) (fcₜ (Var yₓ))) (Var y'ₓ))))))


{- ################################ IO ################################ -}

-- set show-qualified-vars to tt to show if there are bugs in parameter code, because
-- they should always be captured by the scope and unqualified as a binder name
open import to-string (record options {during-elaboration = tt; show-qualified-vars = tt; erase-types = ff; pretty-print = tt})

{-# TERMINATING #-}
cmds-to-string : (newline-before-after : 𝔹) → params → cmds → strM
cmd-to-string : params → cmd → strM
cmd-to-string ps (CmdDefTerm x t) = strBreak 2
  0 [ strVar x >>str strAdd " =" ]
  2 [ to-stringh (lam-expand-term ps t) >>str strAdd "." ]
cmd-to-string ps (CmdDefType x k T) = strBreak 3
  0 [ strVar x >>str strAdd " :" ]
  (3 + string-length x) [ to-stringh (abs-expand-kind ps k) >>str strAdd " =" ]
  2 [ to-stringh (lam-expand-type ps T)  >>str strAdd "." ]
cmd-to-string ps (CmdDefKind x psₖ k) = strBreak 2
  0 [ strVar x ]
  2 [ params-to-string'' (ps ++ psₖ) (to-stringh k) >>str strAdd "." ]
cmd-to-string ps (CmdDefData eds x psₓ k cs) =
  cmds-to-string ff ps (encoding-defs.ecs eds) >>str
  strList 2
    (strBreak 2
      0 [ strAdd "data " >>str strVar x ]
      (5 + string-length x) [ params-to-string'' (ps ++ psₓ)
                                (strAdd ": " >>str to-stringh k) ] ::
     map (uncurry λ x T → strBreak 2
       0 [ strAdd "| " >>str strVar x >>str strAdd " :" ]
       (5 + string-length x) [ to-stringh T ]) cs) >>str strAdd "."
cmd-to-string ps (CmdImport (Import p? fp mn q? as)) =
  strAdd "import " >>str
  strAdd mn >>str
  maybe-else' q? strEmpty (λ x → strAdd " as " >>str strAdd x) >>str
  args-to-string as >>str
  strAdd "."

cmds-to-string b-a ps =
  let b-a-tt : cmd → strM → strM
      b-a-tt = λ c cs → strLine >>str strLine >>str cmd-to-string ps c >>str cs
      b-a-ff : cmd → strM → strM
      b-a-ff = λ c cs → cmd-to-string ps c >>str cs >>str strLine >>str strLine in
  foldr (if b-a then b-a-tt else b-a-ff) strEmpty

file-to-string : file → strM
file-to-string (Module mn ps cs) =
  strAdd "module " >>str
  strAdd mn >>str
  strAdd "." >>str
  cmds-to-string tt [] cs
  --cmds-to-string tt ps cs

record elab-info : Set where
  constructor mk-elab-info
  field
    τ : toplevel-state
    ρ : renamectxt
    φ : renamectxt × trie file
    ν : trie stringset -- dependency mapping

new-elab-info : toplevel-state → elab-info
new-elab-info ts = mk-elab-info ts empty-renamectxt (empty-renamectxt , empty-trie) empty-trie

ts-def : toplevel-state → var → tmtp → toplevel-state
ts-def ts x tT =
  let Γ = toplevel-state.Γ ts
      i = ctxt.i Γ
      d = either-else' tT
            (λ t → term-def nothing opacity-open (just t) (TpHole pi-gen))
            (λ T → type-def nothing opacity-open (just T) (KdHole pi-gen)) in
  record ts { Γ = record Γ { i = trie-insert i x (d , missing-location) } }

add-dep : elab-info → var → elab-info
add-dep (mk-elab-info τ ρ φ ν) mnᵢ =
  let fp = ctxt.fn (toplevel-state.Γ τ)
      mnᵢ-is = stringset-strings (trie-lookup-else empty-trie ν mnᵢ)
      mn-is = trie-lookup-else empty-trie ν fp in
  mk-elab-info τ ρ φ (trie-insert ν fp (foldr (flip stringset-insert) (stringset-insert mn-is mnᵢ) mnᵢ-is))

set-fn : elab-info → filepath → elab-info
set-fn (mk-elab-info τ ρ φ ν) fn = mk-elab-info (record τ { Γ = record (toplevel-state.Γ τ) { fn = fn } }) ρ φ ν

set-mn : elab-info → var → elab-info
set-mn (mk-elab-info τ ρ φ ν) mn = mk-elab-info (record τ { Γ = record (toplevel-state.Γ τ) { mn = mn } }) ρ φ ν

get-fn : elab-info → filepath
get-fn = ctxt.fn ∘' toplevel-state.Γ ∘' elab-info.τ

get-mn : elab-info → var
get-mn = ctxt.mn ∘' toplevel-state.Γ ∘' elab-info.τ

get-deps : elab-info → filepath → file → file
get-deps (mk-elab-info τ ρ φ ν) fp (Module mn ps es) =
  Module mn ps (foldr (λ x → CmdImport (Import ff x (renamectxt-rep (fst φ) x) nothing []) ::_) es (stringset-strings (trie-lookup-else empty-stringset ν fp)))

{-# TERMINATING #-}
elab-file : elab-info → filepath → elab-info × var
elab-cmds : elab-info → params → cmds → elab-info × cmds
elab-cmds ei ps [] = ei , []
elab-cmds ei@(mk-elab-info τ ρ φ ν) ps (CmdDefTerm x t :: csᵣ) =
  rename (get-mn ei # x) - x from ρ for λ x' ρ' →
  let t' = choose-mu (toplevel-state.Γ τ) ρ (params-to-lams ps t) in
  elim elab-cmds (mk-elab-info (ts-def τ x' (Ttm t')) ρ' φ ν) ps csᵣ for λ ei csᵣ →
  ei , CmdDefTerm x' t' :: csᵣ
elab-cmds ei@(mk-elab-info τ ρ φ ν) ps (CmdDefType x k T :: csᵣ) =
  rename (get-mn ei # x) - x from ρ for λ x' ρ' →
  let k' = choose-mu (toplevel-state.Γ τ) ρ (params-to-kind ps k)
      T' = choose-mu (toplevel-state.Γ τ) ρ (params-to-tplams ps T) in
  elim elab-cmds (mk-elab-info (ts-def τ x' (Ttp T')) ρ' φ ν) ps csᵣ for λ ei csᵣ →
  ei , CmdDefType x' k' T' :: csᵣ
elab-cmds ei ps (CmdDefKind x psₖ k :: csᵣ) =
  elab-cmds ei ps csᵣ
elab-cmds ei ps (CmdDefData es x psₓ k cs :: csᵣ) =
  elim elab-cmds ei [] (encoding-defs.ecs es) for λ ei ecs →
  elim elab-cmds ei [] (encoding-defs.gcs es) for λ ei gcs →
  elim elab-cmds ei ps csᵣ for λ ei rcs →
  ei , ecs ++ gcs ++ rcs
elab-cmds ei ps (CmdImport (Import p? fp mn' q? as) :: csᵣ) =
  let fpₒ = get-fn ei; mnₒ = get-mn ei in
  elim elab-file ei fp for λ ei mn'' →
  elab-cmds (add-dep (set-mn (set-fn ei fpₒ) mnₒ) fp) ps csᵣ

elab-file ei @ (mk-elab-info τ ρ φ ν) fp with trie-contains (snd φ) fp
...| tt = ei , renamectxt-rep (fst φ) fp
...| ff with get-include-elt-if τ fp >>= include-elt.ast~
...| nothing = ei , "error"
...| just (Module mn ps es) =
  let p = elab-cmds (record (set-mn (set-fn ei fp) mn) { ν = trie-insert (elab-info.ν ei) fp empty-trie }) ps es
      (mk-elab-info τ ρ φ ν) = fst p
      es' = snd p
      τ = record τ { Γ = record (toplevel-state.Γ τ) { ps = ps } } in
  rename fp - mn from fst φ for λ mn' φ' →
  mk-elab-info τ ρ (φ' , trie-insert (snd φ) fp (Module mn' ps es')) ν , mn'
  
elab-write-all : elab-info → (to : filepath) → IO ⊤
elab-write-all ei@(mk-elab-info τ ρ φ ν) to =
  let Γ = toplevel-state.Γ τ
      print = strRun Γ ∘ file-to-string in
  foldr'
    (createDirectoryIfMissing ff to)
    (uncurry λ fₒ fₛ io → -- fₒ : filepath, fₛ : file
       let fₘ = renamectxt-rep (fst φ) fₒ
           fₙ = combineFileNames to (fₘ ^ ".cdle") in
       io >> writeRopeToFile fₙ (print (get-deps ei fₒ fₛ))
          >> (putStrLn "path:") >> (putStrLn fₙ))
    (trie-mappings (snd φ)) -- 𝕃 (filepath × file) @ (trie file)

elab-all : toplevel-state → (from to : filepath) → IO ⊤
elab-all ts fm to =
--  elab-write-all (fst (elab-file (new-elab-info ts) fm)) to >>
  putStrLn ("0")
