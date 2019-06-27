import cedille-options
module elaboration-helpers (options : cedille-options.options) where

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
--open import spans options {Id}
open import datatype-functions
--open import templates

uncurry' : ∀ {A B C D : Set} → (A → B → C → D) → (A × B × C) → D
uncurry' f (a , b , c) = f a b c

uncurry'' : ∀ {A B C D E : Set} → (A → B → C → D → E) → (A × B × C × D) → E
uncurry'' f (a , b , c , d) = f a b c d

uncurry''' : ∀ {A B C D E F : Set} → (A → B → C → D → E → F) → (A × B × C × D × E) → F
uncurry''' f (a , b , c , d , e) = f a b c d e

ctxt-lookup-term-var' : ctxt → var → maybe type
ctxt-lookup-term-var' Γ @ (mk-ctxt (fn , mn , ps , q) ss is Δ) x =
  env-lookup Γ x >>= λ where
    (term-decl T , _) → just T
    (term-def ps _ _ T , _ , x') →
      let ps = maybe-else [] id ps in
      just $ abs-expand-type ps T
    _ → nothing

-- TODO: Could there be parameter/argument clashes if the same parameter variable is defined multiple times?
-- TODO: Could variables be parameter-expanded multiple times?
ctxt-lookup-type-var' : ctxt → var → maybe kind
ctxt-lookup-type-var' Γ @ (mk-ctxt (fn , mn , ps , q) ss is Δ) x =
  env-lookup Γ x >>= λ where
    (type-decl k , _) → just k
    (type-def ps _ _ k , _ , x') →
      let ps = maybe-else [] id ps in
      just $ abs-expand-kind ps k
    _ → nothing

restore-renamectxt : renamectxt → 𝕃 (var × maybe var) → renamectxt
restore-renamectxt = foldr $ uncurry λ x x' ρ → maybe-else' x' (renamectxt-remove ρ x) (renamectxt-insert ρ x)

restore-ctxt-params : ctxt → 𝕃 (var × maybe qualif-info) → ctxt
restore-ctxt-params = foldr $ uncurry λ x x' Γ → ctxt-set-qualif Γ (maybe-else' x' (trie-remove (ctxt-get-qualif Γ) x) (trie-insert (ctxt-get-qualif Γ) x))

rename-validify : string → string
rename-validify = 𝕃char-to-string ∘ (h ∘ string-to-𝕃char) where
  validify-char : char → 𝕃 char
  validify-char '/' = [ '-' ]
  validify-char c with
    (c =char 'a')  ||
    (c =char 'z')  ||
    (c =char 'A')  ||
    (c =char 'Z')  ||
    (c =char '\'') ||
    (c =char '-')  ||
    (c =char '_')  ||
    is-digit c     ||
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

fresh-id-term : ctxt → term
fresh-id-term Γ = rename "x" from Γ for λ x → mlam x $ Var x

get-renaming : renamectxt → var → var → var × renamectxt
get-renaming ρₓ xₒ x = let x' = fresh-var' x (renamectxt-in-field ρₓ) in x' , renamectxt-insert ρₓ xₒ x'

rename_-_from_for_ : ∀ {X : Set} → var → var → renamectxt → (var → renamectxt → X) → X
rename xₒ - ignored-var from ρₓ for f = f ignored-var ρₓ
rename xₒ - x from ρₓ for f = uncurry f $ get-renaming ρₓ xₒ x

rename_-_lookup_for_ : ∀ {X : Set} → var → var → renamectxt → (var → renamectxt → X) → X
rename xₒ - x lookup ρₓ for f with renamectxt-lookup ρₓ xₒ
...| nothing = rename xₒ - x from ρₓ for f
...| just x' = f x' ρₓ

module reindexing (Γ : ctxt) (D I mn : var) (isₒ : indices) (psₜ : params) where

  reindex-fresh-var : qualif → trie indices → var → var
  reindex-fresh-var ρₓ is ignored-var = ignored-var
  reindex-fresh-var ρₓ is x =
    fresh-h (λ x' → ctxt-binds-var Γ x' || trie-contains is x' || trie-contains ρₓ x') x

  rename-indices' : qualif → trie indices → indices
  rename-indices' ρₓ is = foldr {B = renamectxt → qualif → indices}
    (λ {(Index x atk) f r ρₓ →
       let x' = reindex-fresh-var ρₓ is x in
       Index x' (substh Γ r empty-trie -tk atk) :: f (renamectxt-insert r x x') (trie-insert ρₓ x (x' , []))})
    (λ r ρₓ → []) isₒ empty-renamectxt ρₓ
  
  reindex-t : Set → Set
  reindex-t X = qualif → trie indices → X → X
  
  {-# TERMINATING #-}
  reindex : ∀ {ed} → reindex-t ⟦ ed ⟧
  reindex-term : reindex-t term
  reindex-type : reindex-t type
  reindex-kind : reindex-t kind
  
  reindex{TERM} = reindex-term
  reindex{TYPE} = reindex-type
  reindex{KIND} = reindex-kind

  rc-is : qualif → indices → qualif
  rc-is = foldr λ {(Index x atk) ρₓ → trie-insert ρₓ x (x , [])}

  is-index-var : maybe tpkd → 𝔹
  is-index-var (just (Tkt (TpVar x))) = x =string I
  is-index-var _ = ff
  
  reindex-term ρₓ is (App t (Var x)) with trie-lookup is x
  ...| nothing = App (reindex ρₓ is t) $ reindex ρₓ is $ Var x
  ...| just is' = indices-to-apps is' $ reindex ρₓ is t
  reindex-term ρₓ is (AppEr t (Var x)) with trie-lookup is x
  ...| nothing = AppEr (reindex ρₓ is t) $ reindex ρₓ is $ Var x
  ...| just is' = indices-to-apps is' $ reindex ρₓ is t
  reindex-term ρₓ is (App t t') =
    App (reindex ρₓ is t) (reindex ρₓ is t')
  reindex-term ρₓ is (AppE t tT) =
    AppE (reindex ρₓ is t) (reindex ρₓ is -tT tT)
  reindex-term ρₓ is (Beta t t') =
    Beta (reindex ρₓ is t) (reindex ρₓ is t')
  reindex-term ρₓ is (Delta T t) =
    Delta (reindex ρₓ is T) (reindex ρₓ is t)
  reindex-term ρₓ is (Hole pi) =
    Hole pi
  reindex-term ρₓ is (IotaPair t₁ t₂ x Tₓ) =
    let x' = reindex-fresh-var ρₓ is x in
    IotaPair (reindex ρₓ is t₁) (reindex ρₓ is t₂) x'
      (reindex (trie-insert ρₓ x (x' , [])) is Tₓ)
  reindex-term ρₓ is (IotaProj t n) =
    IotaProj (reindex ρₓ is t) n
  reindex-term ρₓ is (Lam me x tk? t) with is-index-var tk?
  ...| ff = let x' = reindex-fresh-var ρₓ is x in
    Lam me x' (reindex ρₓ is -tk_ <$> tk?) (reindex (trie-insert ρₓ x (x' , [])) is t)
  ...| tt with rename-indices' ρₓ is
  ...| isₙ = indices-to-lams isₙ $ reindex (rc-is ρₓ isₙ) (trie-insert is x isₙ) t
  reindex-term ρₓ is (LetTm me x T? t t') =
    let x' = reindex-fresh-var ρₓ is x in
    LetTm me x' (reindex ρₓ is <$> T?) (reindex ρₓ is t) (reindex (trie-insert ρₓ x (x' , [])) is t')
  reindex-term ρₓ is (LetTp x k T t) =
    let x' = reindex-fresh-var ρₓ is x in
    LetTp x' (reindex ρₓ is k) (reindex ρₓ is T) (reindex (trie-insert ρₓ x (x' , [])) is t)
  reindex-term ρₓ is (Phi t₌ t₁ t₂) =
    Phi (reindex ρₓ is t₌) (reindex ρₓ is t₁) (reindex ρₓ is t₂)
  reindex-term ρₓ is (Rho t₌ x Tₓ t) =
    let x' = reindex-fresh-var ρₓ is x in
    Rho (reindex ρₓ is t) x' (reindex (trie-insert ρₓ x (x' , [])) is Tₓ) (reindex ρₓ is t)
  reindex-term ρₓ is (Sigma t) =
    Sigma (reindex ρₓ is t)
  reindex-term ρₓ is (Var x) =
    maybe-else' (trie-lookup ρₓ x) (Var x) (uncurry (apps-term ∘ Var))
  reindex-term ρₓ is (Mu μ t Tₘ? f~ cs) = Var "template-mu-not-allowed"
  
  reindex-type ρₓ is (TpAbs me x atk T) with is-index-var (just atk)
  ...| ff = let x' = reindex-fresh-var ρₓ is x in
    TpAbs me x' (reindex ρₓ is -tk atk) (reindex (trie-insert ρₓ x (x' , [])) is T)
  ...| tt = let isₙ = rename-indices' ρₓ is in
    indices-to-alls isₙ $ reindex (rc-is ρₓ isₙ) (trie-insert is x isₙ) T
  reindex-type ρₓ is (TpEq t₁ t₂) =
    TpEq (reindex ρₓ is t₁) (reindex ρₓ is t₂)
  reindex-type ρₓ is (TpIota x T T') =
    let x' = reindex-fresh-var ρₓ is x in
    TpIota x' (reindex ρₓ is T) (reindex (trie-insert ρₓ x (x' , [])) is T')
  reindex-type ρₓ is (TpAppTm T (Var x)) with trie-lookup is x
  ...| nothing = TpAppTm (reindex ρₓ is T) $ reindex ρₓ is $ Var x
  ...| just is' = indices-to-tpapps is' $ reindex ρₓ is T
  reindex-type ρₓ is (TpAppTp T (TpVar x)) with trie-lookup is x
  ...| nothing = TpAppTp (reindex ρₓ is T) $ reindex ρₓ is $ TpVar x
  ...| just is' = indices-to-tpapps is' $ reindex ρₓ is T
  reindex-type ρₓ is (TpApp T tT) =
    TpApp (reindex ρₓ is T) (reindex ρₓ is -tT tT)
  reindex-type ρₓ is (TpHole pi) =
    TpHole pi
  reindex-type ρₓ is (TpLam x atk T) with is-index-var (just atk)
  ...| ff = let x' = reindex-fresh-var ρₓ is x in
    TpLam x' (reindex ρₓ is -tk atk) (reindex (trie-insert ρₓ x (x' , [])) is T)
  ...| tt = let isₙ = rename-indices' ρₓ is in
    indices-to-tplams isₙ $ reindex (rc-is ρₓ isₙ) (trie-insert is x isₙ) T
  reindex-type ρₓ is (TpVar x) =
    maybe-else' (trie-lookup ρₓ x) (TpVar x) (uncurry (apps-type ∘ TpVar))
  
  reindex-kind ρₓ is (KdAbs x atk k) with is-index-var (just atk)
  ...| ff = let x' = reindex-fresh-var ρₓ is x in
    KdAbs x' (reindex ρₓ is -tk atk) (reindex (trie-insert ρₓ x (x' , [])) is k)
  ...| tt = let isₙ = rename-indices' ρₓ is in
    indices-to-kind isₙ $ reindex (rc-is ρₓ isₙ) (trie-insert is x isₙ) k
  reindex-kind ρₓ is (KdHole pi) =
    KdHole pi
  reindex-kind ρₓ is KdStar =
    KdStar

  reindex-cmd : qualif → trie indices → cmd → cmd × qualif
  reindex-cmd ρₓ is (CmdImport (Import p? fp mnᵢ q? as)) =
    CmdImport (Import p? fp mnᵢ q? (reindex ρₓ is -arg_ <$> as)) , ρₓ
  reindex-cmd ρₓ is (CmdDefTerm x t) =
    let x' = rename-validify (D ^ "/" ^ x) in
    CmdDefTerm x' (lam-expand-term psₜ $ reindex ρₓ is t) ,
    trie-insert ρₓ (mn # x) (x' , params-to-args psₜ)
  reindex-cmd ρₓ is (CmdDefType x k T) =
    let x' = rename-validify (D ^ "/" ^ x) in
    CmdDefType x' (abs-expand-kind psₜ $ reindex ρₓ is k)
                  (lam-expand-type psₜ $ reindex ρₓ is T) ,
    trie-insert ρₓ (mn # x) (x' , params-to-args psₜ)
  reindex-cmd ρₓ is (CmdDefKind x ps k) =
    CmdDefKind x ps k , ρₓ
  reindex-cmd ρₓ is (CmdDefData es x ps k cs) =
    CmdDefData es x ps k cs , ρₓ
  
  reindex-cmds : qualif → trie indices → cmds → cmds
  reindex-cmds ρₓ is cs =
    foldr
      (λ c rec ρₓ → elim-pair (reindex-cmd ρₓ is c) λ c ρₓ → c :: rec ρₓ)
      (λ ρₓ → []) cs ρₓ

reindex-file : ctxt → (D I modname : var) → indices → params → cmds → cmds
reindex-file Γ D I mn is ps cs =
  let ps' = ctxt-get-current-params Γ ++ params-set-erased Erased ps
      open reindexing Γ D I mn is ps' in
  reindex-cmds empty-trie empty-trie cs


mk-ctr-fmap-t : Set → Set
mk-ctr-fmap-t X = ctxt → (var × var × var × var × term) → X
{-# TERMINATING #-}
mk-ctr-fmap-η+ : mk-ctr-fmap-t (term → type → term)
mk-ctr-fmap-η- : mk-ctr-fmap-t (term → type → term)
mk-ctr-fmap-η? : mk-ctr-fmap-t (term → type → term) → mk-ctr-fmap-t (term → type → term)
mk-ctr-fmapₖ-η+ : mk-ctr-fmap-t (type → kind → type)
mk-ctr-fmapₖ-η- : mk-ctr-fmap-t (type → kind → type)
mk-ctr-fmapₖ-η? : mk-ctr-fmap-t (type → kind → type) → mk-ctr-fmap-t (type → kind → type)

mk-ctr-fmap-η? f Γ x x' T with is-free-in (fst x) T
...| tt = f Γ x x' T
...| ff = x'

mk-ctr-fmapₖ-η? f Γ x x' k with is-free-in (fst x) k
...| tt = f Γ x x' k
...| ff = x'

mk-ctr-fmap-η+ Γ x x' T with decompose-ctr-type Γ T
...| Tₕ , ps , _ =
  params-to-lams ps $
  let Γ' = add-params-to-ctxt ps Γ in
  foldl
    (λ {(Param me x'' (Tkt T)) t →
          (if me then AppEr t else App t) $
            mk-ctr-fmap-η? mk-ctr-fmap-η- Γ' x (Var x'') T;
        (Param _ x'' (Tkk k)) t →
          AppTp t $ mk-ctr-fmapₖ-η? mk-ctr-fmapₖ-η- Γ' x (TpVar x'') k})
    x' ps

mk-ctr-fmapₖ-η+ Γ xₒ @ (x , Aₓ , Bₓ , cₓ , castₓ) x' k =
  let is = kind-to-indices Γ (subst Γ (TpVar Aₓ) x k) in
  indices-to-tplams is $
  let Γ' = add-indices-to-ctxt is Γ in
  foldl
    (λ {(Index x'' (Tkt T)) → flip TpApp $ Ttm $ mk-ctr-fmap-η?  mk-ctr-fmap-η-  Γ' xₒ (Var x'') T;
        (Index x'' (Tkk k)) → flip TpApp $ Ttp $ mk-ctr-fmapₖ-η? mk-ctr-fmapₖ-η- Γ' xₒ (TpVar x'') k})
    x' $ map (λ {(Index x'' atk) → Index x'' $ subst Γ' (TpVar x) Aₓ -tk atk}) is

mk-ctr-fmap-η- Γ xₒ @ (x , Aₓ , Bₓ , cₓ , castₓ) x' T with decompose-ctr-type Γ T
...| TpVar x'' , ps , as =
  params-to-lams ps $
  let Γ' = add-params-to-ctxt ps Γ in
    (if ~ x'' =string x then id else App
      (recompose-apps (tmtps-to-args Erased as) $
        AppEr (AppTp (AppTp castₓ (TpVar Aₓ)) (TpVar Bₓ)) (Var cₓ)))
    (foldl (λ {(Param me x'' (Tkt T)) t →
                 (if me then AppEr t else App t) $
                   mk-ctr-fmap-η? mk-ctr-fmap-η+ Γ' xₒ (Var x'') T;
               (Param me x'' (Tkk k)) t →
                 AppTp t $ mk-ctr-fmapₖ-η? mk-ctr-fmapₖ-η+ Γ' xₒ (TpVar x'') k}) x' ps)
...| TpIota x'' T₁ T₂ , ps , [] =
  let Γ' = add-params-to-ctxt ps Γ
      tₒ = foldl (λ {
            (Param me x'' (Tkt T)) t →
              (if me then AppEr t else App t) $
                mk-ctr-fmap-η? mk-ctr-fmap-η+ Γ' xₒ (Var x'') T;
            (Param me x'' (Tkk k)) t →
              AppTp t $ mk-ctr-fmapₖ-η? mk-ctr-fmapₖ-η+ Γ' xₒ (TpVar x'') k
          }) x' ps
      T₂' = subst Γ (mk-ctr-fmap-η? mk-ctr-fmap-η- Γ' xₒ (Var x'') T₁) x'' T₂
      t₁ = mk-ctr-fmap-η? mk-ctr-fmap-η- Γ' xₒ (IotaProj tₒ ι1) T₁
      t₂ = mk-ctr-fmap-η? mk-ctr-fmap-η- Γ' xₒ (IotaProj tₒ ι2) T₂' in
  params-to-lams ps $ IotaPair t₁ t₂ x'' T₂'
...| Tₕ , ps , as = x'

mk-ctr-fmapₖ-η- Γ xₒ @ (x , Aₓ , Bₓ , cₓ , castₓ) x' k with kind-to-indices Γ (subst Γ (TpVar Bₓ) x k)
...| is =
  indices-to-tplams is $
  let Γ' = add-indices-to-ctxt is Γ in
  foldl (λ {(Index x'' (Tkt T)) → flip TpApp $ Ttm $ mk-ctr-fmap-η? mk-ctr-fmap-η+ Γ' xₒ (Var x'') T;
            (Index x'' (Tkk k)) → flip TpApp $ Ttp $ mk-ctr-fmapₖ-η? mk-ctr-fmapₖ-η+ Γ' xₒ (TpVar x'') k})
    x' $ map (λ {(Index x'' atk) → Index x'' $ subst Γ' (TpVar x) Bₓ -tk atk}) is


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
encode-datatype Γ eds @ (mk-enc-defs ecs
                               Cast cast-in cast-out cast-is
                               Functor functor-in functor-out
                               Fix fix-in fix-out
                               lambek1 lambek2 fix-ind)
                  (Data Dₓ ps is cs) =
  record eds {ecs = ecs ++ [: TypeF-cmd ⌟ IndF-cmd ⌟ fmap-cmd ⌟ D-cmd ⌟ Is-cmd ⌟ is-cmd ⌟ to-cmd ⌟ map ctr-cmd cs :] }
  where
  mk-ctr-eterm : params → var → term
  mk-ctr-eterm ps x =
    let xs = erase-params ps in
    Beta id-term $ foldr
      mlam
      (foldl (flip App ∘ Var) (Var x) xs)
      (xs ++ map fst cs)
  
  mk-ctr-ftype : ctxt → ctr → var → type
  mk-ctr-ftype Γ (Ctr x T) X with decompose-ctr-type (ctxt-var-decl X Γ) T
  ...| Tₕ , as , rs =
    params-to-alls as $
    TpApp (recompose-tpapps rs $ TpVar X) $ Ttm $
    Beta id-term (mk-ctr-eterm as x)
  
  mk-ftype2 : ctxt → (ιₓ : var) → type
  mk-ftype2 Γ ιₓ =
    rename "X" from Γ for λ X →
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
    TpAbs tt X (Tkk $ indices-to-kind is $ KdAbs ignored-var (Tkt top-type) KdStar) $
    foldr
      (λ c → TpAbs ff ignored-var $ Tkt $ mk-ctr-ftype Γ c X)
      (TpApp (indices-to-tpapps is $ TpVar X) $ Ttm $ Var ιₓ)
      cs

  Γₚₛ = ctxt-get-current-params Γ
  psₑ = params-set-erased Erased ps
  psₜ = Γₚₛ ++ psₑ

  app-ps = params-to-apps psₜ ∘ Var
  tpapp-ps = params-to-tpapps psₜ ∘ TpVar

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


  TypeF-cmd = CmdDefType (data-TypeF/ Dₓ)
                (params-to-kind psₜ $ KdAbs ignored-var tkᵢ kᵢ) $
    let Γ' = add-indices-to-ctxt is $ add-params-to-ctxt ps Γ in
    rename "x" from Γ' for λ ιₓ →
    {-
    λ p₁ : P₁. λ p₂ : P₂. ...
      λ Dₓ : Π i₁ : I₁. Π i₂ : I₂. ... ★.
        λ i₁ : I₁. λ i₂ : I₂. ...
          ι ιₓ : Top. mk-ftype2 (ctxt-var-decl ιₓ Γ') ιₓ.
    -}
    params-to-tplams ps $
      TpLam Dₓ (Tkk $ indices-to-kind is KdStar) $
        indices-to-tplams is $
          TpIota ιₓ top-type $ mk-ftype2 (ctxt-var-decl ιₓ Γ') ιₓ

  
  fmap-cmd = CmdDefTerm (data-fmap/ Dₓ) $
    rename "A" from Γ for λ Aₓ →
    rename "B" from Γ for λ Bₓ →
    rename "c" from Γ for λ cₓ →
    rename "x" from Γ for λ xₓ →
    rename "X" from Γ for λ Xₓ →
    params-to-lams psₜ $
    AppEr (AppTp functor-in TypeF/D) $
    Lam tt Aₓ jtkᵢ $
    Lam tt Bₓ jtkᵢ $
    Lam tt cₓ (just (Tkt (TpAppTp (TpAppTp Cast (TpVar Aₓ)) (TpVar Bₓ)))) $
    IotaPair
      (indices-to-lams is $
       Lam ff xₓ (just (Tkt TypeF/D)) $
       IotaPair (IotaProj (Var xₓ) ι1)
         (Lam tt Xₓ jtkᵢ $
          flip (foldr $ uncurry λ x T → Lam ff x (just (Tkt
                   (mk-ctr-ftype (decl-Γ Γ [: Aₓ ⌟ Bₓ ⌟ cₓ ⌟ xₓ ⌟ Xₓ :]) (x , T) Xₓ)))) cs $
          foldl
            (flip App ∘ uncurry
              (mk-ctr-fmap-η+
                (decl-Γ Γ [: Aₓ ⌟ Bₓ ⌟ cₓ :])
                (Dₓ , Aₓ , Bₓ , cₓ , cast-out)
               ∘ Var))
            (AppTp (IotaProj (Var xₓ) ι2) (TpVar Xₓ))
            cs)
        xₓ (mk-ftype2 (decl-Γ Γ [: Aₓ ⌟ Bₓ ⌟ cₓ :]) xₓ))
      (Beta id-term id-term)
      xₓ (TpEq (Var xₓ) id-term)

  IndF-cmd = CmdDefTerm (data-IndF/ Dₓ) $
    params-to-lams psₜ $
    Lam tt Dₓ jtkᵢ $
    indices-to-lams is $
    rename "x" from Γ for λ xₓ →
    rename "y" from Γ for λ yₓ →
    rename "e" from Γ for λ eₓ →
    rename "X" from Γ for λ Xₓ →
    let T = indices-to-tpapps is (TpAppTp Functor (TpVar Dₓ)) in
    Lam ff xₓ (just $ Tkt T) $
    Lam tt Xₓ (just $ Tkk $ indices-to-kind is $ KdAbs ignored-var (Tkt T) KdStar) $
    flip (foldr λ c → Lam ff (fst c) (just (Tkt (mk-ctr-ftype Γ c Xₓ)))) cs $
    flip AppEr (Beta (Var xₓ) id-term) $
    flip AppEr (Var xₓ) $
    let Γ' = decl-Γ Γ [: xₓ ⌟ yₓ ⌟ eₓ ⌟ Xₓ :] in
    flip (foldl $ uncurry λ x' T' →
      elim-pair (decompose-arrows Γ' T') λ as Tₕ →
      flip App $
      params-to-lams as $
      Lam tt yₓ (just (Tkt T)) $
      Lam tt eₓ (just (Tkt (TpEq (Var yₓ) (mk-ctr-eterm as x')))) $
      params-to-apps as $
      Var x') cs $
    AppTp (IotaProj (Var xₓ) ι2) $
    indices-to-tplams is $
    TpLam xₓ (Tkt top-type) $
    TpAbs tt yₓ (Tkt T) $
    TpAbs tt eₓ (Tkt $ TpEq (Var yₓ) (Var xₓ)) $
    TpAppTm (indices-to-tpapps is $ TpVar Xₓ) $
    Phi (Var eₓ) (Var yₓ) (Var xₓ)

  D-cmd = CmdDefType Dₓ (params-to-kind ps kᵢ) $
    params-to-tplams psₜ $
    TpAppTm (TpApp Fix (Ttp TypeF/D)) fmap/D

  is-projn : var → type → type
  is-projn Xₓ T =
    rename "i" from add-params-to-ctxt ps Γ for λ iₓ →
    TpIota iₓ
      (indices-to-alls is
        (TpAbs ff ignored-var (Tkt (indices-to-tpapps is (TpVar Xₓ)))
          (indices-to-tpapps is T)))
      (TpEq (Var iₓ) id-term)

  is-proj1 = λ Xₓ → is-projn Xₓ D
  is-proj2 = λ Xₓ → is-projn Xₓ (TpApp TypeF/D (Ttp (TpVar Xₓ)))

  is-proj' : var → term → term
  is-proj' Xₓ mu =
    let t = App (AppTp mu D)
              (Lam ff "c" (just (Tkt (is-proj1 Xₓ)))
                (Lam ff "o" (just (Tkt (is-proj2 Xₓ)))
                  (Var "c"))) in
    Phi (IotaProj t ι2) (IotaProj t ι1) id-term

  Is-cmd = CmdDefType (data-Is/ Dₓ) (params-to-kind ps $ KdAbs ignored-var tkᵢ KdStar) $
    params-to-tplams (Γₚₛ ++ ps) $
    rename "X" from add-params-to-ctxt ps Γ for λ Xₓ →
    rename "Y" from add-params-to-ctxt ps Γ for λ Yₓ →
    TpLam Xₓ tkᵢ $
    TpAbs tt Yₓ (Tkk KdStar) $
    TpAbs ff ignored-var
      (Tkt (TpAbs ff ignored-var (Tkt (is-proj1 Xₓ)) $
            TpAbs ff ignored-var (Tkt (is-proj2 Xₓ)) $
            TpVar Yₓ))
      (TpVar Yₓ)

  is-cmd = CmdDefTerm (data-is/ Dₓ) $
    params-to-lams (Γₚₛ ++ ps) $
    rename "Y" from add-params-to-ctxt ps Γ for λ Yₓ →
    rename "f" from add-params-to-ctxt ps Γ for λ fₓ →
    let pair = λ t → IotaPair t (Beta (erase t) (erase t)) "x" (TpEq (Var "x") (erase t)) in
    Lam tt Yₓ (just (Tkk KdStar)) $
    Lam ff fₓ (just (Tkt (TpAbs ff ignored-var (Tkt (is-proj1 Yₓ)) $
                          TpAbs ff ignored-var (Tkt (is-proj2 Yₓ)) $
                          TpVar Yₓ))) $
    App (App (Var fₓ) (pair (indices-to-lams is id-term)))
        (pair (AppEr (AppTp fix-out TypeF/D) fmap/D))

  to-cmd = CmdDefTerm (data-to/ Dₓ) $
    rename "Y" from add-params-to-ctxt ps Γ for λ Yₓ →
    rename "mu" from add-params-to-ctxt ps Γ for λ muₓ →
    params-to-lams (Γₚₛ ++ ps) $
    Lam tt Yₓ jtkᵢ $
    Lam tt muₓ (just (Tkt (TpApp Is/D (Ttp (TpVar Yₓ))))) $
    is-proj' Yₓ (Var muₓ)

  ctr-cmd : ctr → cmd
  ctr-cmd (Ctr x' T) with subst Γ D Dₓ T
  ...| T' with decompose-ctr-type Γ T'
  ...| Tₕ , as , rs = CmdDefTerm x' $
    let Γ' = add-params-to-ctxt as Γ in
    rename "X" from Γ' for λ Xₓ →
    rename "x" from Γ' for λ xₓ →
    let tₖ = indices-to-kind is (KdAbs ignored-var (Tkt top-type) KdStar)
        t = Lam tt Xₓ (just (Tkk tₖ)) (foldr
                (uncurry λ x T → Lam ff x (just (Tkt (mk-ctr-ftype Γ' (Ctr x' T) Xₓ))))
                (params-to-apps as (Var x')) cs) in
    params-to-lams (Γₚₛ ++ ps) $
    params-to-lams as $
    App (recompose-apps (tmtps-to-args tt $ drop (length ps) rs) $
          AppEr (AppTp fix-in TypeF/D) fmap/D) $
    IotaPair (Beta id-term (erase t)) t xₓ (mk-ftype2 Γ' xₓ)


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
      return (encode-datatype Γ (mk-enc-defs (reverse mcs)
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


{-


{- Datatypes -}


mendler-elab-mu-pure : ctxt → ctxt-datatype-info → encoded-datatype-names → maybe var → term → cases → maybe term
mendler-elab-mu-pure Γ (mk-data-info X is/X? asₚ asᵢ ps kᵢ k cs fcs) (mk-encoded-datatype-names _ _ _ _ _ _ _ _ fixpoint-inₓ fixpoint-outₓ fixpoint-indₓ fixpoint-lambekₓ) x? t ms =
  
  let ps-tm = id --λ t → foldr (const $ flip App id-term) t $ erase-params ps
      fix-ind = Var fixpoint-indₓ -- hnf Γ unfold-all (ps-tm $ Var fixpoint-indₓ) tt
      fix-out = Var fixpoint-outₓ -- hnf Γ unfold-all (ps-tm $ Var fixpoint-outₓ) tt
      μ-tm = λ x msf → App (App fix-ind t) $ mlam x $ rename "x" from ctxt-var-decl x Γ for λ fₓ → mlam fₓ $ msf $ Var fₓ -- App fix-out $ Var fₓ
      μ'-tm = λ msf → msf $ App fix-out t
      set-nth = λ l n a → foldr{B = maybe ℕ → 𝕃 (maybe term)}
        (λ {a' t nothing → a' :: t nothing;
            a' t (just zero) → a :: t nothing;
            a' t (just (suc n)) → a' :: t (just n)})
        (λ _ → []) l (just n) in
  -- Note: removing the implicit arguments below hangs Agda's type-checker!
  foldl{B = 𝕃 (maybe term) → maybe (term → term)}
    (λ c msf l → case_of_{B = maybe (term → term)} c
       λ {(Case _ x cas t) → env-lookup Γ ("//" ^ x) >>=
         λ {(ctr-def ps? _ n i a , _ , _) →
           msf (set-nth l i (just $ caseArgs-to-lams cas t)); _ → nothing}})
    (-- Note: lambda-expanding this "foldr..." also hangs Agda...?
     foldr (λ t? msf → msf >>= λ msf → t? >>= λ t →
              just λ t' → (msf (App t' t))) (just λ t → t))
    ms (map (λ _ → nothing) ms) >>= (just ∘ maybe-else' x? μ'-tm μ-tm)

mendler-elab-mu : elab-mu-t
mendler-elab-mu Γ (mk-data-info X is/X? asₚ asᵢ ps kᵢ k cs fcs)
  (mk-encoded-datatype-names
    data-functorₓ data-fmapₓ data-Muₓ data-muₓ data-castₓ data-functor-indₓ castₓ
    fixpoint-typeₓ fixpoint-inₓ fixpoint-outₓ fixpoint-indₓ fixpoint-lambekₓ)
   Xₒ x? t Tₘ ms =
  let infixl 10 _-is _-ps _`ps _·is _·ps
      _-is = recompose-apps $ ttys-to-args tt asᵢ
      _`ps = recompose-apps asₚ
      _-ps = recompose-apps $ args-set-erased tt asₚ
      _·is = recompose-tpapps asᵢ
      _·ps = recompose-tpapps $ args-to-ttys asₚ
      σ = fst (mk-inst ps (asₚ ++ ttys-to-args ff asᵢ))
      is = kind-to-indices Γ (substs Γ σ k)
      Γᵢₛ = add-indices-to-ctxt is $ add-params-to-ctxt ps Γ
      is-as : indices → args
      is-as = map λ {(Index x atk) →
        tk-elim atk (λ _ → TermArg tt $ ₓ x) (λ _ → TypeArg $ ₓ x)}
      is/X? = maybe-map ₓ_ is/X? maybe-or either-else' x? (λ _ → nothing) (maybe-map fst)
      --open? = Open OpacTrans X
      --close? = Open OpacOpaque X
      ms' = foldr (λ {(Case _ x cas t) σ →
              let Γ' = add-caseArgs-to-ctxt cas Γᵢₛ in
              trie-insert σ x $ caseArgs-to-lams cas $
              rename "y" from Γ' for λ yₓ →
              rename "e" from Γ' for λ eₓ →
              Λ yₓ ₊ Λ eₓ ₊ close X - (ρ (ς ₓ eₓ) - t)}) empty-trie ms
      fmap = ₓ data-fmapₓ `ps
      functor = ₓ data-functorₓ ·ps
      Xₜₚ = ₓ X ·ps
      in-fix = λ is/X? T asᵢ t → either-else' x? (λ x → recompose-apps asᵢ (ₓ fixpoint-inₓ -ps · functor - fmap) ` (maybe-else' is/X? t λ is/X →
        recompose-apps asᵢ (ₓ castₓ -ps - (fmap · T · Xₜₚ - (open` data-Muₓ - (is/X ` (λ` "to" ₊ λ` "out" ₊ ₓ "to"))))) ` t)) (λ e → maybe-else' (is/X? maybe-or maybe-map fst e) t λ is/X → recompose-apps asᵢ (ₓ castₓ -ps · ₓ Xₒ · Xₜₚ - (open` data-Muₓ - (is/X ` (λ` "to" ₊ λ` "out" ₊ ₓ "to")))) ` t)
      app-lambek = λ is/X? t T asᵢ body → body - (in-fix is/X? T asᵢ t) -
        (recompose-apps asᵢ (ₓ fixpoint-lambekₓ -ps · functor - fmap) ` (in-fix is/X? T asᵢ t)) in
  rename "x" from Γᵢₛ for λ xₓ →
  rename "y" from Γᵢₛ for λ yₓ →
  rename "y'" from ctxt-var-decl yₓ Γᵢₛ for λ y'ₓ →
  rename "z" from Γᵢₛ for λ zₓ →
  rename "e" from Γᵢₛ for λ eₓ →
  rename "X" from Γᵢₛ for λ Xₓ →
  maybe-else (just $ Var "1" , Γ) just $
  foldl (λ {(Ctr _ x Tₓ) rec → rec >>= λ rec → trie-lookup ms' x >>= λ t →
    just λ tₕ → rec tₕ ` t}) (just λ t → t) cs >>= λ msf →
  maybe-else (just $ Var "2" , Γ) just $
  just $ flip (either-else' x?)

    (λ _ → open` X - (app-lambek is/X? t (ₓ Xₒ ·ps) (ttys-to-args tt asᵢ) (msf
      (let Tₛ = maybe-else' is/X? Xₜₚ λ _ → ₓ Xₒ
           fcₜ = maybe-else' is/X? id λ is/X → _`_ $ indices-to-apps is $
             ₓ castₓ -ps · (functor · Tₛ) · (functor · Xₜₚ) -
               (fmap · Tₛ · Xₜₚ - (open` data-Muₓ - (is/X ` (λ` "to" ₊ λ` "out" ₊ ₓ "to"))))
           out = maybe-else' is/X? (ₓ fixpoint-outₓ -ps · functor - fmap) λ is/X →
             let i = open` data-Muₓ - is/X · (ι xₓ :` indices-to-alls is (indices-to-tpapps is Tₛ ➔ indices-to-tpapps is (functor · Tₛ)) ₊ [ ₓ xₓ ≃ ₓ fixpoint-outₓ ]) ` (λ` "to" ₊ λ` "out" ₊ ₓ "out") in
             φ i ₊2 - i ₊1 [ ₓ fixpoint-outₓ ] in
      (φ β - (ₓ data-functor-indₓ `ps · Tₛ -is ` (out -is ` t)) [ ₓ fixpoint-outₓ ` |` t `| ])
        · (indices-to-tplams is $ λ` yₓ :` indices-to-tpapps is (functor · Tₛ) ₊
           ∀` y'ₓ :` indices-to-tpapps is Xₜₚ ₊ ∀` eₓ :` [ ₓ fixpoint-inₓ -ps ` ₓ yₓ ≃ ₓ y'ₓ ] ₊
           indices-to-tpapps is Tₘ ` (φ ₓ eₓ -
             (indices-to-apps is (ₓ fixpoint-inₓ -ps · functor - fmap) ` (fcₜ (ₓ yₓ))) [ ₓ y'ₓ ]))))) , Γ)

    λ xₒ → rename xₒ from Γᵢₛ for λ x →
    let Rₓₒ = mu-Type/ x
        isRₓₒ = mu-isType/ x in
    rename Rₓₒ from Γᵢₛ for λ Rₓ →
    rename isRₓₒ from Γᵢₛ for λ isRₓ →
    rename "to" from Γᵢₛ for λ toₓ →
    rename "out" from Γᵢₛ for λ outₓ →
    let fcₜ = ₓ castₓ -ps · (functor · ₓ Rₓ) · (functor · Xₜₚ) - (fmap · ₓ Rₓ · Xₜₚ - ₓ toₓ)
        subst-msf = subst-renamectxt Γᵢₛ (maybe-extract
          (renamectxt-insert* empty-renamectxt (xₒ :: isRₓₒ :: Rₓₒ :: toₓ :: outₓ :: xₓ :: yₓ :: y'ₓ :: []) (x :: isRₓ :: Rₓ :: toₓ :: outₓ :: xₓ :: yₓ :: y'ₓ :: [])) refl) ∘ msf in
    open` X - (ₓ fixpoint-indₓ -ps · functor - fmap -is ` t · Tₘ `
      (Λ Rₓ  ₊ Λ toₓ ₊ Λ outₓ ₊ λ` x ₊
       indices-to-lams is (λ` yₓ ₊
       -[ isRₓ :` ₓ data-Muₓ ·ps · (ₓ Rₓ) =`
           open` data-Muₓ - (Λ ignored-var ₊ λ` xₓ ₊ ₓ xₓ ` (ₓ toₓ) ` (ₓ outₓ))]-
       (app-lambek (just $ ₓ isRₓ) (ₓ yₓ) (ₓ Rₓ) (is-as is) $ subst-msf
         ((φ β - (indices-to-apps is (ₓ data-functor-indₓ `ps · (ₓ Rₓ)) ` ₓ yₓ) [ ₓ yₓ ]) ·
           (indices-to-tplams is $ λ` yₓ :` indices-to-tpapps is (functor · (ₓ Rₓ)) ₊
             ∀` y'ₓ :` indices-to-tpapps is Xₜₚ ₊ ∀` eₓ :` [ ₓ fixpoint-inₓ -ps ` ₓ yₓ ≃ ₓ y'ₓ ] ₊
             indices-to-tpapps is Tₘ ` (φ ₓ eₓ -
               (indices-to-apps is (ₓ fixpoint-inₓ -ps · functor - fmap) ` (indices-to-apps is fcₜ ` (ₓ yₓ)))
               [ ₓ y'ₓ ]))))))) , ctxt-datatype-decl' X isRₓ Rₓ asₚ Γ
-}



{- ################################ IO ###################################### -}

open import to-string (record options {during-elaboration = tt; show-qualified-vars = ff; erase-types = ff; pretty-print = tt})

{-# TERMINATING #-}
cmds-to-string : (newline-before-after : 𝔹) → cmds → strM
cmd-to-string : cmd → strM
cmd-to-string (CmdDefTerm x t) = strBreak 2
  0 [ strVar x >>str strAdd " =" ]
  2 [ to-stringh t >>str strAdd "." ]
cmd-to-string (CmdDefType x k T) = strBreak 3
  0 [ strVar x >>str strAdd " :" ]
  (3 + string-length x) [ to-stringh k >>str strAdd " =" ]
  2 [ to-stringh T  >>str strAdd "." ]
cmd-to-string (CmdDefKind x ps k) = strBreak 2
  0 [ strVar x ]
  2 [ params-to-string'' ps (to-stringh k) >>str strAdd "." ]
cmd-to-string (CmdDefData eds x ps k cs) =
  cmds-to-string ff (encoding-defs.ecs eds) >>str
  strList 2
    (strBreak 2
      0 [ strAdd "data " >>str strVar x ]
      (5 + string-length x) [ params-to-string'' ps (strAdd ": " >>str to-stringh k) ] ::
     map (uncurry λ x T → strBreak 2
       0 [ strAdd "| " >>str strVar x >>str strAdd " :" ]
       (5 + string-length x) [ to-stringh T ]) cs) >>str strAdd "."
cmd-to-string (CmdImport (Import p? fp mn q? as)) =
  strAdd "import " >>str
  strAdd mn >>str
  maybe-else' q? strEmpty (λ x → strAdd " as " >>str strAdd x) >>str
  args-to-string as >>str
  strAdd "."

cmds-to-string b-a =
  let b-a-tt : cmd → strM → strM
      b-a-tt = λ c cs → strLine >>str strLine >>str cmd-to-string c >>str cs
      b-a-ff : cmd → strM → strM
      b-a-ff = λ c cs → cmd-to-string c >>str cs >>str strLine >>str strLine in
  foldr (if b-a then b-a-tt else b-a-ff) strEmpty

file-to-string : file → strM
file-to-string (Module mn ps cs) =
  strList 2 ((strAdd "module " >>str strAdd mn) ::
             (params-to-string'' ps (strAdd ".")) :: []) >>str
  cmds-to-string tt cs

record elab-info : Set where
  constructor mk-elab-info
  field
    τ : toplevel-state
    ρ : renamectxt
    φ : renamectxt × trie file

new-elab-info : toplevel-state → elab-info
new-elab-info ts = mk-elab-info ts empty-renamectxt (empty-renamectxt , empty-trie)

{-# TERMINATING #-}
elab-file : elab-info → filepath → elab-info × var
elab-cmds : elab-info → (modname : var) → cmds → elab-info × cmds
elab-cmds ei mn [] = ei , []
elab-cmds (mk-elab-info τ ρ φ) mn (CmdDefTerm x t :: csᵣ) =
  rename (mn # x) - x from ρ for λ x' ρ' →
  elim-pair (elab-cmds (mk-elab-info τ ρ' φ) mn csᵣ) λ ei csᵣ →
  ei , CmdDefTerm x' (subst-renamectxt (toplevel-state.Γ τ) ρ t) :: csᵣ
elab-cmds (mk-elab-info τ ρ φ) mn (CmdDefType x k T :: csᵣ) =
  rename (mn # x) - x from ρ for λ x' ρ' →
  elim-pair (elab-cmds (mk-elab-info τ ρ' φ) mn csᵣ) λ ei csᵣ →
  ei , CmdDefType x' (subst-renamectxt (toplevel-state.Γ τ) ρ k)
                     (subst-renamectxt (toplevel-state.Γ τ) ρ T) :: csᵣ
elab-cmds ei mn (CmdDefKind x ps k :: csᵣ) =
  elab-cmds ei mn csᵣ
elab-cmds ei mn (CmdDefData es x ps k cs :: csᵣ) =
  elim-pair (elab-cmds ei mn (encoding-defs.ecs es)) λ ei es →
  let (mk-elab-info τ ρ φ) = ei in
  rename (mn # x) - x from ρ for λ x' ρ' →
--  elim-pair (foldr {B = renamectxt → ctrs × renamectxt}
--    (uncurry λ x T rec ρ →
--     rename (mn # x) - x from ρ for λ x' ρ' →
--     elim-pair (rec ρ') λ cs ρ'' →
--     Ctr x' (subst-renamectxt (toplevel-state.Γ τ) ρ T) :: cs , ρ'')
--    (λ ρ → [] , ρ) cs ρ') λ cs ρ' →
  elim-pair (elab-cmds ei mn csᵣ) λ ei csᵣ →
  ei , (es ++ csᵣ)
elab-cmds ei mn (CmdImport (Import p? fp mn' q? as) :: csᵣ) =
  elim-pair (elab-file ei fp) λ ei mn'' →
  elim-pair (elab-cmds ei mn csᵣ) λ ei csᵣ →
  ei , CmdImport (Import Private fp mn'' nothing []) :: csᵣ


elab-file ei @ (mk-elab-info τ ρ φ) fp with trie-contains (snd φ) fp
...| tt = ei , renamectxt-rep (fst φ) fp
...| ff with get-include-elt-if τ fp >>= include-elt.ast~
...| nothing = ei , "error"
...| just (Module mn _ es) =
  let p = elab-cmds ei mn es
      (mk-elab-info τ ρ φ) = fst p
      es' = snd p in
  rename fp - mn from fst φ for λ mn' φ' →
  mk-elab-info τ ρ (φ' , trie-insert (snd φ) fp (Module mn' [] es')) , mn'

elab-write-all : elab-info → (to : filepath) → IO ⊤
elab-write-all (mk-elab-info τ ρ φ) to =
  let Γ = toplevel-state.Γ τ
      print = strRun Γ ∘ file-to-string in
  foldr'
    (createDirectoryIfMissing ff to)
    (uncurry λ fₒ fₛ io →
       let fₘ = renamectxt-rep (fst φ) fₒ
           fₙ = combineFileNames to (fₘ ^ ".cdle") in
       io >> writeRopeToFile fₙ (print fₛ))
    (trie-mappings (snd φ))

elab-all : toplevel-state → (from to : filepath) → IO ⊤
elab-all ts fm to =
  elab-write-all (fst (elab-file (new-elab-info ts) fm)) to >>
  putStrLn "0"
