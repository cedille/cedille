import cedille-options
module elaboration-helpers (options : cedille-options.options) where

open import lib
open import monad-instances
open import general-util
open import cedille-types
open import syntax-util
open import ctxt
open import conversion
open import constants
open import to-string options
open import subst
open import rename
open import is-free
open import toplevel-state options {id}
open import spans options {id}
open import datatype-functions
open import templates
open import erase

uncurry' : ∀ {A B C D : Set} → (A → B → C → D) → (A × B × C) → D
uncurry' f (a , b , c) = f a b c

uncurry'' : ∀ {A B C D E : Set} → (A → B → C → D → E) → (A × B × C × D) → E
uncurry'' f (a , b , c , d) = f a b c d

uncurry''' : ∀ {A B C D E F : Set} → (A → B → C → D → E → F) → (A × B × C × D × E) → F
uncurry''' f (a , b , c , d , e) = f a b c d e

ctxt-term-decl' : posinfo → var → type → ctxt → ctxt
ctxt-term-decl' pi x T (mk-ctxt (fn , mn , ps , q) ss is os Δ) =
  mk-ctxt (fn , mn , ps , trie-insert q x (x , [])) ss
    (trie-insert is x (term-decl T , fn , pi)) os Δ

ctxt-type-decl' : posinfo → var → kind → ctxt → ctxt
ctxt-type-decl' pi x k (mk-ctxt (fn , mn , ps , q) ss is os Δ) =
  mk-ctxt (fn , mn , ps , trie-insert q x (x , [])) ss
    (trie-insert is x (type-decl k , fn , pi)) os Δ

ctxt-tk-decl' : posinfo → var → tk → ctxt → ctxt
ctxt-tk-decl' pi x (Tkt T) = ctxt-term-decl' pi x T
ctxt-tk-decl' pi x (Tkk k) = ctxt-type-decl' pi x k

ctxt-param-decl : var → var → tk → ctxt → ctxt
ctxt-param-decl x x' atk Γ @ (mk-ctxt (fn , mn , ps , q) ss is os Δ) =
  let d = case atk of λ {(Tkt T) → term-decl T; (Tkk k) → type-decl k} in
  mk-ctxt
  (fn , mn , ps , trie-insert q x (x , [])) ss
  (trie-insert is x' (d , fn , pi-gen)) os Δ

ctxt-term-def' : var → var → term → type → opacity → ctxt → ctxt
ctxt-term-def' x x' t T op Γ @ (mk-ctxt (fn , mn , ps , q) ss is os Δ) = mk-ctxt
  (fn , mn , ps , qualif-insert-params q (mn # x) x ps) ss
  (trie-insert is x' (term-def (just ps) op (just $ hnf Γ unfold-head t tt) T , fn , x)) os Δ

ctxt-type-def' : var → var → type → kind → opacity → ctxt → ctxt
ctxt-type-def' x x' T k op Γ @ (mk-ctxt (fn , mn , ps , q) ss is os Δ) = mk-ctxt
  (fn , mn , ps , qualif-insert-params q (mn # x) x ps) ss
  (trie-insert is x' (type-def (just ps) op (just $ hnf Γ (unfolding-elab unfold-head) T tt) k , fn , x)) os Δ

ctxt-let-term-def : posinfo → var → term → type → ctxt → ctxt
ctxt-let-term-def pi x t T Γ @ (mk-ctxt (fn , mn , ps , q) ss is os Δ) =
  mk-ctxt (fn , mn , ps , trie-insert q x (x , [])) ss
    (trie-insert is x (term-def nothing OpacTrans (just $ hnf Γ unfold-head t tt) T , fn , pi)) os Δ

ctxt-let-type-def : posinfo → var → type → kind → ctxt → ctxt
ctxt-let-type-def pi x T k Γ @ (mk-ctxt (fn , mn , ps , q) ss is os Δ) =
  mk-ctxt (fn , mn , ps , trie-insert q x (x , [])) ss
    (trie-insert is x (type-def nothing OpacTrans (just $ hnf Γ (unfolding-elab unfold-head) T tt) k , fn , pi)) os Δ
{-
ctxt-μ-out-def : var → term → term → var → ctxt → ctxt
ctxt-μ-out-def x t c y (mk-ctxt mod ss is os Δ) =
  let is' = is --trie-insert is y (term-udef nothing OpacTrans c , "missing" , "missing")
      is'' = trie-insert is' x (term-udef nothing OpacTrans t , y , y) in
  mk-ctxt mod ss is'' os Δ
-}


ctxt-datatype-decl' : var → var → var → args → ctxt → ctxt
ctxt-datatype-decl' X isType/v Type/v as Γ@(mk-ctxt (fn , mn , ps , q) ss is os (Δ , μ' , μ)) =
  mk-ctxt (fn , mn , ps , q) ss is os $ Δ , trie-insert μ' Type/v (X , isType/v , as) , μ
  --mk-ctxt (fn , mn , ps , q) ss (trie-insert is ("/" ^ Type/v) $ rename-def ("/" ^ X) , "missing" , "missing") os $ Δ , trie-insert μ' Type/v (X , isType/v , as) , μ

{-
ctxt-rename-def' : var → var → args → ctxt → ctxt
ctxt-rename-def' x x' as (mk-ctxt (fn , mn , ps , q) ss is os Δ) = mk-ctxt (fn , mn , ps , trie-insert q x (x' , as)) ss (trie-insert is x (rename-def x' , "missing" , "missing")) os Δ
-}

ctxt-kind-def' : var → var → params → kind → ctxt → ctxt
ctxt-kind-def' x x' ps2 k Γ @ (mk-ctxt (fn , mn , ps1 , q) ss is os Δ) = mk-ctxt
  (fn , mn , ps1 , qualif-insert-params q (mn # x) x ps1) ss
  (trie-insert is x' (kind-def (ps1 ++ qualif-params Γ ps2) k' , fn , pi-gen)) os Δ
  where
  k' = hnf Γ (unfolding-elab unfold-head) k tt

{-
ctxt-datatype-def' : var → var → params → kind → kind → ctrs → ctxt → ctxt
ctxt-datatype-def' x x' psᵢ kᵢ k cs Γ@(mk-ctxt (fn , mn , ps , q) ss is os (Δ , μₓ)) = mk-ctxt
  (fn , mn , ps , q') ss
  (trie-insert is x' (type-def (just $ ps ++ psᵢ) OpacTrans nothing k , fn , x)) os
  (trie-insert Δ x' (ps ++ psᵢ , kᵢ , k , cs) , μₓ)
  where
  q' = qualif-insert-params q x x' ps
-}

ctxt-lookup-term-var' : ctxt → var → maybe type
ctxt-lookup-term-var' Γ @ (mk-ctxt (fn , mn , ps , q) ss is os Δ) x =
  env-lookup Γ x ≫=maybe λ where
    (term-decl T , _) → just T
    (term-def ps _ _ T , _ , x') →
      let ps = maybe-else [] id ps in
      just $ abs-expand-type ps T
    _ → nothing

-- TODO: Could there be parameter/argument clashes if the same parameter variable is defined multiple times?
-- TODO: Could variables be parameter-expanded multiple times?
ctxt-lookup-type-var' : ctxt → var → maybe kind
ctxt-lookup-type-var' Γ @ (mk-ctxt (fn , mn , ps , q) ss is os Δ) x =
  env-lookup Γ x ≫=maybe λ where
    (type-decl k , _) → just k
    (type-def ps _ _ k , _ , x') →
      let ps = maybe-else [] id ps in
      just $ abs-expand-kind ps k
    _ → nothing

subst-qualif : ∀ {ed : exprd} → ctxt → renamectxt → ⟦ ed ⟧ → ⟦ ed ⟧
subst-qualif{TERM} Γ ρₓ = subst-renamectxt Γ ρₓ ∘ qualif-term Γ
subst-qualif{TYPE} Γ ρₓ = subst-renamectxt Γ ρₓ ∘ qualif-type Γ
subst-qualif{KIND} Γ ρₓ = subst-renamectxt Γ ρₓ ∘ qualif-kind Γ
subst-qualif Γ ρₓ = id

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
fresh-var' : string → (string → 𝔹) → renamectxt → string
fresh-var' = fresh-var ∘ rename-validify

rename-new_from_for_ : ∀ {X : Set} → var → ctxt → (var → X) → X
rename-new "_" from Γ for f = f $ fresh-var' "x" (ctxt-binds-var Γ) empty-renamectxt
rename-new x from Γ for f = f $ fresh-var' x (ctxt-binds-var Γ) empty-renamectxt

rename_from_for_ : ∀ {X : Set} → var → ctxt → (var → X) → X
rename "_" from Γ for f = f "_"
rename x from Γ for f = f $ fresh-var' x (ctxt-binds-var Γ) empty-renamectxt

fresh-id-term : ctxt → term
fresh-id-term Γ = rename "x" from Γ for λ x → mlam x $ mvar x

get-renaming : renamectxt → var → var → var × renamectxt
get-renaming ρₓ xₒ x = let x' = fresh-var' x (renamectxt-in-range ρₓ) ρₓ in x' , renamectxt-insert ρₓ xₒ x'

rename_-_from_for_ : ∀ {X : Set} → var → var → renamectxt → (var → renamectxt → X) → X
rename xₒ - "_" from ρₓ for f = f "_" ρₓ
rename xₒ - x from ρₓ for f = uncurry f $ get-renaming ρₓ xₒ x

rename_-_lookup_for_ : ∀ {X : Set} → var → var → renamectxt → (var → renamectxt → X) → X
rename xₒ - x lookup ρₓ for f with renamectxt-lookup ρₓ xₒ
...| nothing = rename xₒ - x from ρₓ for f
...| just x' = f x' ρₓ

qualif-new-var : ctxt → var → var
qualif-new-var Γ x = ctxt-get-current-modname Γ # x

ctxt-datatype-def' : var → var → var → params → kind → kind → ctrs → ctxt → ctxt
ctxt-datatype-def' v Is/v is/v psᵢ kᵢ k cs Γ@(mk-ctxt (fn , mn , ps , q) ss i os (Δ , μ' , μ)) =
  mk-ctxt (fn , mn , ps , q) ss i os
    (trie-insert Δ v (ps ++ psᵢ , kᵢ , k , cs) ,
     trie-insert μ' elab-mu-prev-key (v , is/v , []) ,
     trie-insert μ Is/v v)

mbeta : term → term → term
mrho : term → var → type → term → term
mtpeq : term → term → type
mbeta t t' = Beta pi-gen (SomeTerm t pi-gen) (SomeTerm t' pi-gen)
mrho t x T t' = Rho pi-gen RhoPlain NoNums t (Guide pi-gen x T) t'
mtpeq t1 t2 = TpEq pi-gen t1 t2 pi-gen
{-
subst-args-params : ctxt → args → params → kind → kind
subst-args-params Γ (ArgsCons (TermArg _ t) ys) (ParamsCons (Decl _ _ _ x _ _) ps) k =
  subst-args-params Γ ys ps $ subst Γ t x k
subst-args-params Γ (ArgsCons (TypeArg t) ys) (ParamsCons (Decl _ _ _ x _ _) ps) k =
  subst-args-params Γ ys ps $ subst Γ t x k
subst-args-params Γ ys ps k = k
-}


module reindexing (Γ : ctxt) (isₒ : indices) where

  reindex-fresh-var : renamectxt → trie indices → var → var
  reindex-fresh-var ρₓ is "_" = "_"
  reindex-fresh-var ρₓ is x =
    fresh-var x (λ x' → ctxt-binds-var Γ x' || trie-contains is x') ρₓ

  rename-indices : renamectxt → trie indices → indices
  rename-indices ρₓ is = foldr {B = renamectxt → indices}
    (λ {(Index x atk) f ρₓ →
       let x' = reindex-fresh-var ρₓ is x in
       Index x' (substh-tk {TERM} Γ ρₓ empty-trie atk) :: f (renamectxt-insert ρₓ x x')})
    (λ ρₓ → []) isₒ ρₓ

  reindex-subst : ∀ {ed} → ⟦ ed ⟧ → ⟦ ed ⟧
  reindex-subst {ed} = substs {ed} {TERM} Γ empty-trie
  
  reindex-t : Set → Set
  reindex-t X = renamectxt → trie indices → X → X
  
  {-# TERMINATING #-}
  reindex : ∀ {ed} → reindex-t ⟦ ed ⟧
  reindex-term : reindex-t term
  reindex-type : reindex-t type
  reindex-kind : reindex-t kind
  reindex-tk : reindex-t tk
  reindex-liftingType : reindex-t liftingType
  reindex-optTerm : reindex-t optTerm
  reindex-optType : reindex-t optType
  reindex-optGuide : reindex-t optGuide
  reindex-optClass : reindex-t optClass
  reindex-lterms : reindex-t lterms
  reindex-args : reindex-t args
  reindex-arg : reindex-t arg
  reindex-theta : reindex-t theta
  reindex-vars : reindex-t (maybe vars)
  reindex-defTermOrType : renamectxt → trie indices → defTermOrType → defTermOrType × renamectxt
  
  reindex{TERM} = reindex-term
  reindex{TYPE} = reindex-type
  reindex{KIND} = reindex-kind
  reindex{TK}   = reindex-tk
  reindex       = λ ρₓ is x → x

  rc-is : renamectxt → indices → renamectxt
  rc-is = foldr λ {(Index x atk) ρₓ → renamectxt-insert ρₓ x x}
  
  index-var = "indices"
  index-type-var = "Indices"
  is-index-var = isJust ∘ is-pfx index-var
  is-index-type-var = isJust ∘ is-pfx index-type-var
  
  reindex-term ρₓ is (App t me (Var pi x)) with trie-lookup is x
  ...| nothing = App (reindex-term ρₓ is t) me (reindex-term ρₓ is (Var pi x))
  ...| just is' = indices-to-apps is' $ reindex-term ρₓ is t
  reindex-term ρₓ is (App t me t') =
    App (reindex-term ρₓ is t) me (reindex-term ρₓ is t')
  reindex-term ρₓ is (AppTp t T) =
    AppTp (reindex-term ρₓ is t) (reindex-type ρₓ is T)
  reindex-term ρₓ is (Beta pi ot ot') =
    Beta pi (reindex-optTerm ρₓ is ot) (reindex-optTerm ρₓ is ot')
  reindex-term ρₓ is (Chi pi oT t) =
    Chi pi (reindex-optType ρₓ is oT) (reindex-term ρₓ is t)
  reindex-term ρₓ is (Delta pi oT t) =
    Delta pi (reindex-optType ρₓ is oT) (reindex-term ρₓ is t)
  reindex-term ρₓ is (Epsilon pi lr m t) =
    Epsilon pi lr m (reindex-term ρₓ is t)
  reindex-term ρₓ is (Hole pi) =
    Hole pi
  reindex-term ρₓ is (IotaPair pi t t' g pi') =
    IotaPair pi (reindex-term ρₓ is t) (reindex-term ρₓ is t') (reindex-optGuide ρₓ is g) pi'
  reindex-term ρₓ is (IotaProj t n pi) =
    IotaProj (reindex-term ρₓ is t) n pi
  reindex-term ρₓ is (Lam pi me pi' x oc t) with is-index-var x
  ...| ff = let x' = reindex-fresh-var ρₓ is x in
    Lam pi me pi' x' (reindex-optClass ρₓ is oc) (reindex-term (renamectxt-insert ρₓ x x') is t)
  ...| tt with rename-indices ρₓ is | oc
  ...| isₙ | NoClass = indices-to-lams' isₙ $ reindex-term (rc-is ρₓ isₙ) (trie-insert is x isₙ) t
  ...| isₙ | SomeClass atk = indices-to-lams isₙ $ reindex-term (rc-is ρₓ isₙ) (trie-insert is x isₙ) t
  reindex-term ρₓ is (Let pi fe d t) =
    elim-pair (reindex-defTermOrType ρₓ is d) λ d' ρₓ' → Let pi fe d' (reindex-term ρₓ' is t)
  reindex-term ρₓ is (Open pi o pi' x t) =
    Open pi o pi' x (reindex-term ρₓ is t)
  reindex-term ρₓ is (Parens pi t pi') =
    reindex-term ρₓ is t
  reindex-term ρₓ is (Phi pi t₌ t₁ t₂ pi') =
    Phi pi (reindex-term ρₓ is t₌) (reindex-term ρₓ is t₁) (reindex-term ρₓ is t₂) pi'
  reindex-term ρₓ is (Rho pi op on t og t') =
    Rho pi op on (reindex-term ρₓ is t) (reindex-optGuide ρₓ is og) (reindex-term ρₓ is t')
  reindex-term ρₓ is (Sigma pi t) =
    Sigma pi (reindex-term ρₓ is t)
  reindex-term ρₓ is (Theta pi θ t ts) =
    Theta pi (reindex-theta ρₓ is θ) (reindex-term ρₓ is t) (reindex-lterms ρₓ is ts)
  reindex-term ρₓ is (Var pi x) =
    Var pi $ renamectxt-rep ρₓ x
  reindex-term ρₓ is (Mu pi pi' x t oT pi'' cs pi''') = Var pi-gen "template-mu-not-allowed"
  reindex-term ρₓ is (Mu' pi ot t oT pi' cs pi'') = Var pi-gen "template-mu-not-allowed" 
  
  reindex-type ρₓ is (Abs pi me pi' x atk T) with is-index-var x
  ...| ff = let x' = reindex-fresh-var ρₓ is x in
    Abs pi me pi' x' (reindex-tk ρₓ is atk) (reindex-type (renamectxt-insert ρₓ x x') is T)
  ...| tt = let isₙ = rename-indices ρₓ is in
    indices-to-alls isₙ $ reindex-type (rc-is ρₓ isₙ) (trie-insert is x isₙ) T
  reindex-type ρₓ is (Iota pi pi' x T T') =
    let x' = reindex-fresh-var ρₓ is x in
    Iota pi pi' x' (reindex-type ρₓ is T) (reindex-type (renamectxt-insert ρₓ x x') is T')
  reindex-type ρₓ is (Lft pi pi' x t lT) =
    let x' = reindex-fresh-var ρₓ is x in
    Lft pi pi' x' (reindex-term (renamectxt-insert ρₓ x x') is t) (reindex-liftingType ρₓ is lT)
  reindex-type ρₓ is (NoSpans T pi) =
    NoSpans (reindex-type ρₓ is T) pi
  reindex-type ρₓ is (TpLet pi d T) =
    elim-pair (reindex-defTermOrType ρₓ is d) λ d' ρₓ' → TpLet pi d' (reindex-type ρₓ' is T)
  reindex-type ρₓ is (TpApp T T') =
    TpApp (reindex-type ρₓ is T) (reindex-type ρₓ is T')
  reindex-type ρₓ is (TpAppt T (Var pi x)) with trie-lookup is x
  ...| nothing = TpAppt (reindex-type ρₓ is T) (reindex-term ρₓ is (Var pi x))
  ...| just is' = indices-to-tpapps is' $ reindex-type ρₓ is T
  reindex-type ρₓ is (TpAppt T t) =
    TpAppt (reindex-type ρₓ is T) (reindex-term ρₓ is t)
  reindex-type ρₓ is (TpArrow (TpVar pi x) Erased T) with is-index-type-var x
  ...| ff = TpArrow (reindex-type ρₓ is (TpVar pi x)) Erased (reindex-type ρₓ is T)
  ...| tt = let isₙ = rename-indices ρₓ is in
    indices-to-alls isₙ $ reindex-type (rc-is ρₓ isₙ) is T
  reindex-type ρₓ is (TpArrow T me T') =
    TpArrow (reindex-type ρₓ is T) me (reindex-type ρₓ is T')
  reindex-type ρₓ is (TpEq pi t t' pi') =
    TpEq pi (reindex-term ρₓ is t) (reindex-term ρₓ is t') pi'
  reindex-type ρₓ is (TpHole pi) =
    TpHole pi
  reindex-type ρₓ is (TpLambda pi pi' x atk T) with is-index-var x
  ...| ff = let x' = reindex-fresh-var ρₓ is x in
    TpLambda pi pi' x' (reindex-tk ρₓ is atk) (reindex-type (renamectxt-insert ρₓ x x') is T)
  ...| tt = let isₙ = rename-indices ρₓ is in
    indices-to-tplams isₙ $ reindex-type (rc-is ρₓ isₙ) (trie-insert is x isₙ) T
  reindex-type ρₓ is (TpParens pi T pi') =
    reindex-type ρₓ is T
  reindex-type ρₓ is (TpVar pi x) =
    TpVar pi $ renamectxt-rep ρₓ x
  
  reindex-kind ρₓ is (KndParens pi k pi') =
    reindex-kind ρₓ is k
  reindex-kind ρₓ is (KndArrow k k') =
    KndArrow (reindex-kind ρₓ is k) (reindex-kind ρₓ is k')
  reindex-kind ρₓ is (KndPi pi pi' x atk k) with is-index-var x
  ...| ff = let x' = reindex-fresh-var ρₓ is x in
    KndPi pi pi' x' (reindex-tk ρₓ is atk) (reindex-kind (renamectxt-insert ρₓ x x') is k)
  ...| tt = let isₙ = rename-indices ρₓ is in
    indices-to-kind isₙ $ reindex-kind (rc-is ρₓ isₙ) (trie-insert is x isₙ) k
  reindex-kind ρₓ is (KndTpArrow (TpVar pi x) k) with is-index-type-var x
  ...| ff = KndTpArrow (reindex-type ρₓ is (TpVar pi x)) (reindex-kind ρₓ is k)
  ...| tt = let isₙ = rename-indices ρₓ is in
    indices-to-kind isₙ $ reindex-kind (rc-is ρₓ isₙ) is k
  reindex-kind ρₓ is (KndTpArrow T k) =
    KndTpArrow (reindex-type ρₓ is T) (reindex-kind ρₓ is k)
  reindex-kind ρₓ is (KndVar pi x as) =
    KndVar pi (renamectxt-rep ρₓ x) (reindex-args ρₓ is as)
  reindex-kind ρₓ is (Star pi) =
    Star pi
  
  reindex-tk ρₓ is (Tkt T) = Tkt $ reindex-type ρₓ is T
  reindex-tk ρₓ is (Tkk k) = Tkk $ reindex-kind ρₓ is k
  
  -- Can't reindex large indices in a lifting type (LiftPi requires a type, not a tk),
  -- so for now we will just ignore reindexing lifting types.
  -- Types withing lifting types will still be reindexed, though.
  reindex-liftingType ρₓ is (LiftArrow lT lT') =
    LiftArrow (reindex-liftingType ρₓ is lT) (reindex-liftingType ρₓ is lT')
  reindex-liftingType ρₓ is (LiftParens pi lT pi') =
    reindex-liftingType ρₓ is lT
  reindex-liftingType ρₓ is (LiftPi pi x T lT) =
    let x' = reindex-fresh-var ρₓ is x in
    LiftPi pi x' (reindex-type ρₓ is T) (reindex-liftingType (renamectxt-insert ρₓ x x') is lT)
  reindex-liftingType ρₓ is (LiftStar pi) =
    LiftStar pi
  reindex-liftingType ρₓ is (LiftTpArrow T lT) =
    LiftTpArrow (reindex-type ρₓ is T) (reindex-liftingType ρₓ is lT)
  
  reindex-optTerm ρₓ is NoTerm = NoTerm
  reindex-optTerm ρₓ is (SomeTerm t pi) = SomeTerm (reindex-term ρₓ is t) pi
  
  reindex-optType ρₓ is NoType = NoType
  reindex-optType ρₓ is (SomeType T) = SomeType (reindex-type ρₓ is T)
  
  reindex-optClass ρₓ is NoClass = NoClass
  reindex-optClass ρₓ is (SomeClass atk) = SomeClass (reindex-tk ρₓ is atk)
  
  reindex-optGuide ρₓ is NoGuide = NoGuide
  reindex-optGuide ρₓ is (Guide pi x T) =
    let x' = reindex-fresh-var ρₓ is x in
    Guide pi x' (reindex-type (renamectxt-insert ρₓ x x') is T)
  
  reindex-lterms ρₓ is = map λ where
    (Lterm me t) → Lterm me (reindex-term ρₓ is t)

  reindex-theta ρₓ is (AbstractVars xs) = maybe-else Abstract AbstractVars $ reindex-vars ρₓ is $ just xs
  reindex-theta ρₓ is θ = θ

  reindex-vars''' : vars → vars → vars
  reindex-vars''' (VarsNext x xs) xs' = VarsNext x $ reindex-vars''' xs xs'
  reindex-vars''' (VarsStart x) xs = VarsNext x xs
  reindex-vars'' : vars → maybe vars
  reindex-vars'' (VarsNext x (VarsStart x')) = just $ VarsStart x
  reindex-vars'' (VarsNext x xs) = maybe-map (VarsNext x) $ reindex-vars'' xs
  reindex-vars'' (VarsStart x) = nothing
  reindex-vars' : renamectxt → trie indices → var → maybe vars
  reindex-vars' ρₓ is x = maybe-else (just $ VarsStart $ renamectxt-rep ρₓ x)
    (reindex-vars'' ∘ flip foldr (VarsStart "") λ {(Index x atk) → VarsNext x}) (trie-lookup is x)
  reindex-vars ρₓ is (just (VarsStart x)) = reindex-vars' ρₓ is x
  reindex-vars ρₓ is (just (VarsNext x xs)) = maybe-else (reindex-vars ρₓ is $ just xs)
    (λ xs' → maybe-map (reindex-vars''' xs') $ reindex-vars ρₓ is $ just xs) $ reindex-vars' ρₓ is x
  reindex-vars ρₓ is nothing = nothing
  
  reindex-arg ρₓ is (TermArg me t) = TermArg me (reindex-term ρₓ is t)
  reindex-arg ρₓ is (TypeArg T) = TypeArg (reindex-type ρₓ is T)
  reindex-args ρₓ is = map(reindex-arg ρₓ is)
  
  reindex-defTermOrType ρₓ is (DefTerm pi x oT t) =
    let x' = reindex-fresh-var ρₓ is x
        oT' = optType-map oT reindex-subst in
    DefTerm elab-hide-key x' (reindex-optType ρₓ is oT') (reindex-term ρₓ is $ reindex-subst t) , renamectxt-insert ρₓ x x'
  reindex-defTermOrType ρₓ is (DefType pi x k T) =
    let x' = reindex-fresh-var ρₓ is x in
    DefType elab-hide-key x' (reindex-kind ρₓ is $ reindex-subst k) (reindex-type ρₓ is $ reindex-subst T) , renamectxt-insert ρₓ x x'

  reindex-cmds : renamectxt → trie indices → cmds → cmds × renamectxt
  reindex-cmds ρₓ is [] = [] , ρₓ
  reindex-cmds ρₓ is ((ImportCmd i) :: cs) =
    elim-pair (reindex-cmds ρₓ is cs) $ _,_ ∘ _::_ (ImportCmd i)
  reindex-cmds ρₓ is ((DefTermOrType op d pi) :: cs) =
    elim-pair (reindex-defTermOrType ρₓ is d) λ d' ρₓ' →
    elim-pair (reindex-cmds ρₓ' is cs) $ _,_ ∘ _::_ (DefTermOrType op d' pi)
  reindex-cmds ρₓ is ((DefKind pi x ps k pi') :: cs) =
    let x' = reindex-fresh-var ρₓ is x in
    elim-pair (reindex-cmds (renamectxt-insert ρₓ x x') is cs) $ _,_ ∘ _::_
      (DefKind pi x' ps (reindex-kind ρₓ is $ reindex-subst k) pi')
  reindex-cmds ρₓ is ((DefDatatype dt pi) :: cs) =
    reindex-cmds ρₓ is cs -- Templates can't use datatypes!

reindex-file : ctxt → indices → start → cmds × renamectxt
reindex-file Γ is (File csᵢ pi' pi'' x ps cs pi''') =
  reindex-cmds empty-renamectxt empty-trie cs
  where open reindexing Γ is

parameterize-file : ctxt → params → cmds → cmds
parameterize-file Γ ps cs = foldr {B = qualif → cmds}
  (λ c cs σ → elim-pair (h c σ) λ c σ → c :: cs σ) (λ _ → []) cs empty-trie
  where
  ps' = ps -- substs-params {ARG} Γ empty-trie ps
  σ+ = λ σ x → qualif-insert-params σ x x ps'

  subst-ps : ∀ {ed} → qualif → ⟦ ed ⟧ → ⟦ ed ⟧
  subst-ps = substs $ add-params-to-ctxt ps' Γ

  h' : defTermOrType → qualif → defTermOrType × qualif
  h' (DefTerm pi x T? t) σ =
    let T?' = case T? of λ where
                (SomeType T) → SomeType $ abs-expand-type ps' $ subst-ps σ T
                NoType → NoType
        t' = params-to-lams ps' $ subst-ps σ t in
    DefTerm pi x T?' t' , σ+ σ x
  h' (DefType pi x k T) σ =
    let k' = abs-expand-kind ps' $ subst-ps σ k
        T' = params-to-tplams ps' $ subst-ps σ T in
    DefType pi x k' T' , σ+ σ x

  h : cmd → qualif → cmd × qualif
  h (ImportCmd i) σ = ImportCmd i , σ
  h (DefTermOrType op d pi) σ = elim-pair (h' d σ) λ d σ → DefTermOrType op d pi , σ
  h (DefKind pi x ps'' k pi') σ = DefKind pi x ps'' k pi' , σ
  h (DefDatatype dt pi) σ = DefDatatype dt pi , σ


open import cedille-syntax

mk-ctr-term : maybeErased → (x X : var) → ctrs → params → term
mk-ctr-term me x X cs ps =
  let t = Mlam X $ ctrs-to-lams' cs $ params-to-apps ps $ mvar x in
  case me of λ where
    Erased → Beta pi-gen NoTerm $ SomeTerm t pi-gen
    NotErased → IotaPair pi-gen (Beta pi-gen NoTerm $ SomeTerm t pi-gen)
                  t NoGuide pi-gen

mk-ctr-type : maybeErased → ctxt → ctr → ctrs → var → type
mk-ctr-type me Γ (Ctr _ x T) cs Tₕ with decompose-ctr-type (ctxt-var-decl Tₕ Γ) T
...| Tₓ , ps , is =
  params-to-alls ps $
  TpAppt (recompose-tpapps is $ mtpvar Tₕ) $
  rename "X" from add-params-to-ctxt ps (ctxt-var-decl Tₕ Γ) for λ X →
  mk-ctr-term me x X cs ps


mk-ctr-fmap-t : Set → Set
mk-ctr-fmap-t X = ctxt → (var × var × var × var × term) → X
{-# TERMINATING #-}
mk-ctr-fmap-η+ : mk-ctr-fmap-t (term → type → term)
mk-ctr-fmap-η- : mk-ctr-fmap-t (term → type → term)
mk-ctr-fmap-η? : mk-ctr-fmap-t (term → type → term) → mk-ctr-fmap-t (term → type → term)
mk-ctr-fmapₖ-η+ : mk-ctr-fmap-t (type → kind → type)
mk-ctr-fmapₖ-η- : mk-ctr-fmap-t (type → kind → type)
mk-ctr-fmapₖ-η? : mk-ctr-fmap-t (type → kind → type) → mk-ctr-fmap-t (type → kind → type)

mk-ctr-fmap-η? f Γ x x' T with is-free-in tt (fst x) T
...| tt = f Γ x x' T
...| ff = x'

mk-ctr-fmapₖ-η? f Γ x x' k with is-free-in tt (fst x) k
...| tt = f Γ x x' k
...| ff = x'

mk-ctr-fmap-η+ Γ x x' T with decompose-ctr-type Γ T
...| Tₕ , ps , _ =
  params-to-lams' ps $
  let Γ' = add-params-to-ctxt ps Γ in
  foldl
    (λ {(Decl _ _ me x'' (Tkt T) _) t → App t me $ mk-ctr-fmap-η? mk-ctr-fmap-η- Γ' x (mvar x'') T;
        (Decl _ _ _ x'' (Tkk k) _) t → AppTp t $ mk-ctr-fmapₖ-η? mk-ctr-fmapₖ-η- Γ' x (mtpvar x'') k})
    x' ps

mk-ctr-fmapₖ-η+ Γ xₒ @ (x , Aₓ , Bₓ , cₓ , castₓ) x' k =
  let is = kind-to-indices Γ (subst Γ (mtpvar Aₓ) x k) in
  indices-to-tplams is $
  let Γ' = add-indices-to-ctxt is Γ in
  foldl
    (λ {(Index x'' (Tkt T)) → flip TpAppt $ mk-ctr-fmap-η?  mk-ctr-fmap-η-  Γ' xₒ (mvar x'') T;
        (Index x'' (Tkk k)) → flip TpApp  $ mk-ctr-fmapₖ-η? mk-ctr-fmapₖ-η- Γ' xₒ (mtpvar x'') k})
    x' $ map (λ {(Index x'' atk) → Index x'' $ subst Γ' (mtpvar x) Aₓ atk}) is

mk-ctr-fmap-η- Γ xₒ @ (x , Aₓ , Bₓ , cₓ , castₓ) x' T with decompose-ctr-type Γ T
...| TpVar _ x'' , ps , as =
  params-to-lams' ps $
  let Γ' = add-params-to-ctxt ps Γ in
    (if ~ x'' =string x then id else mapp
      (recompose-apps (ttys-to-args Erased as) $
        mappe (AppTp (AppTp castₓ (mtpvar Aₓ)) (mtpvar Bₓ)) (mvar cₓ)))
    (foldl (λ {(Decl _ _ me x'' (Tkt T) _) t →
                 App t me $ mk-ctr-fmap-η? mk-ctr-fmap-η+ Γ' xₒ (mvar x'') T;
               (Decl _ _ me x'' (Tkk k) _) t →
                 AppTp t $ mk-ctr-fmapₖ-η? mk-ctr-fmapₖ-η+ Γ' xₒ (mtpvar x'') k}) x' ps)
...| Iota _ _ x'' T₁ T₂ , ps , [] =
  let Γ' = add-params-to-ctxt ps Γ
      tₒ = foldl (λ {
            (Decl _ _ me x'' (Tkt T) _) t →
              App t me $ mk-ctr-fmap-η? mk-ctr-fmap-η+ Γ' xₒ (mvar x'') T;
            (Decl _ _ me x'' (Tkk k) _) t →
              AppTp t $ mk-ctr-fmapₖ-η? mk-ctr-fmapₖ-η+ Γ' xₒ (mtpvar x'') k
          }) x' ps
      t₁ = mk-ctr-fmap-η? mk-ctr-fmap-η- Γ' xₒ (IotaProj tₒ "1" pi-gen) T₁
      t₂ = mk-ctr-fmap-η? mk-ctr-fmap-η- Γ' xₒ (IotaProj tₒ "2" pi-gen)
             (subst Γ (mk-ctr-fmap-η? mk-ctr-fmap-η- Γ' xₒ (mvar x'') T₁) x'' T₂) in
  params-to-lams' ps $ IotaPair pi-gen t₁ t₂ NoGuide pi-gen
...| Tₕ , ps , as = x'

mk-ctr-fmapₖ-η- Γ xₒ @ (x , Aₓ , Bₓ , cₓ , castₓ) x' k with kind-to-indices Γ (subst Γ (mtpvar Bₓ) x k)
...| is =
  indices-to-tplams is $
  let Γ' = add-indices-to-ctxt is Γ in
  foldl (λ {(Index x'' (Tkt T)) → flip TpAppt $ mk-ctr-fmap-η? mk-ctr-fmap-η+ Γ' xₒ (mvar x'') T;
            (Index x'' (Tkk k)) → flip TpApp $ mk-ctr-fmapₖ-η? mk-ctr-fmapₖ-η+ Γ' xₒ (mtpvar x'') k})
    x' $ map (λ {(Index x'' atk) → Index x'' $ subst Γ' (mtpvar x) Bₓ atk}) is

record encoded-datatype-names : Set where
  constructor mk-encoded-datatype-names
  field
    data-functor : var
    data-fmap : var
    data-Mu : var
    data-mu : var
    data-cast : var
    data-functor-ind : var
    cast : var
    fixpoint-type : var
    fixpoint-in : var
    fixpoint-out : var
    fixpoint-ind : var
    fixpoint-lambek : var

elab-mu-t : Set
elab-mu-t = ctxt → ctxt-datatype-info → encoded-datatype-names → var → var ⊎ maybe (term × var × 𝕃 tty) → term → type → cases → maybe (term × ctxt)

record encoded-datatype : Set where
  constructor mk-encoded-datatype
  field
    --data-def : datatype
    --mod-ps : params
    names : encoded-datatype-names
    elab-mu : elab-mu-t
    elab-mu-pure : ctxt → ctxt-datatype-info → maybe var → term → cases → maybe term

  check-mu : ctxt → ctxt-datatype-info → var → var ⊎ maybe (term × var × 𝕃 tty) → term → optType → cases → type → maybe (term × ctxt)
  check-mu Γ d Xₒ x? t oT ms T with d --data-def
  check-mu Γ d Xₒ x? t oT ms T | mk-data-info X mu asₚ asᵢ ps kᵢ k cs fcs -- Data X ps is cs
    with kind-to-indices Γ kᵢ | oT
  check-mu Γ d Xₒ x? t oT ms T | mk-data-info X mu asₚ asᵢ ps kᵢ k cs fcs | is | NoType =
    elab-mu Γ {-(Data X ps is cs)-} d names Xₒ x? t
      (indices-to-tplams is $ TpLambda pi-gen pi-gen ignored-var
        (Tkt $ indices-to-tpapps is $ flip apps-type asₚ $ mtpvar X) T) ms
  check-mu Γ d Xₒ x? t oT ms T | mk-data-info X mu asₚ asᵢ ps kᵢ k cs fcs | is | SomeType Tₘ =
    elab-mu Γ d names Xₒ x? t Tₘ ms

  synth-mu : ctxt → ctxt-datatype-info → var → var ⊎ maybe (term × var × 𝕃 tty) → term → optType → cases → maybe (term × ctxt)
  synth-mu Γ d Xₒ x? t NoType ms = nothing
  synth-mu Γ d Xₒ x? t (SomeType Tₘ) ms = elab-mu Γ d names Xₒ x? t Tₘ ms

record datatype-encoding : Set where
  constructor mk-datatype-encoding
  field
    template : start
    functor : var
    cast : var
    fixpoint-type : var
    fixpoint-in : var
    fixpoint-out : var
    fixpoint-ind : var
    fixpoint-lambek : var
    elab-mu : elab-mu-t
    elab-mu-pure : ctxt → ctxt-datatype-info → encoded-datatype-names → maybe var → term → cases → maybe term

  {-# TERMINATING #-}
  mk-defs : ctxt → datatype → cmds × cmds × encoded-datatype
  mk-defs Γ'' (Data x ps is cs) =
    tcs ,
    (csn OpacTrans functor-cmd $
     csn OpacTrans functor-ind-cmd $
     csn OpacTrans fmap-cmd $
     csn OpacOpaque type-cmd $
     csn OpacOpaque Mu-cmd $
     csn OpacTrans mu-cmd $
     csn OpacTrans cast-cmd $
     foldr (csn OpacTrans ∘ ctr-cmd) [] cs) ,
    record {
      elab-mu = elab-mu;
      elab-mu-pure = λ Γ d → elab-mu-pure Γ d namesₓ;
      --data-def = Data x ps is cs;
      --mod-ps = ctxt-get-current-params Γ;
      names = namesₓ}
    where
    csn : opacity → defTermOrType → cmds → cmds
    csn o d = DefTermOrType o d pi-gen ::_

    k = indices-to-kind is $ Star pi-gen
    
    Γ' = add-params-to-ctxt ps $ add-ctrs-to-ctxt cs $ ctxt-var-decl x Γ''
    
    tcs-ρ = reindex-file Γ' is template
    tcs = parameterize-file Γ' (params-set-erased Erased $ {-ctxt-get-current-params Γ'' ++-} ps) $ fst tcs-ρ
    ρₓ = snd tcs-ρ

    data-functorₓ = fresh-var (x ^ "F") (ctxt-binds-var Γ') ρₓ
    data-fmapₓ = fresh-var (x ^ "Fmap") (ctxt-binds-var Γ') ρₓ
    --data-fresh-check = λ f → fresh-var x (λ x → ctxt-binds-var Γ' (f x) || renamectxt-in-field ρₓ (rename-validify $ f x) || renamectxt-in-field ρₓ (f x) || renamectxt-in-field ρₓ (rename-validify $ f x)) ρₓ
    data-Muₓₒ = x -- data-fresh-check data-Is/
    data-muₓₒ = x -- data-fresh-check data-is/
    data-castₓₒ = x -- data-fresh-check data-to/
    data-Muₓ = data-Is/ data-Muₓₒ
    data-muₓ = data-is/ data-muₓₒ
    data-castₓ = data-to/ data-castₓₒ
    data-Muₓᵣ = rename-validify data-Muₓ
    data-muₓᵣ = rename-validify data-muₓ
    data-castₓᵣ = rename-validify data-castₓ
    data-functor-indₓ = fresh-var (x ^ "IndF") (ctxt-binds-var Γ') ρₓ
    functorₓ = renamectxt-rep ρₓ functor
    castₓ = renamectxt-rep ρₓ cast
    fixpoint-typeₓ = renamectxt-rep ρₓ fixpoint-type
    fixpoint-inₓ = renamectxt-rep ρₓ fixpoint-in
    fixpoint-outₓ = renamectxt-rep ρₓ fixpoint-out
    fixpoint-indₓ = renamectxt-rep ρₓ fixpoint-ind
    fixpoint-lambekₓ = renamectxt-rep ρₓ fixpoint-lambek
    Γ = foldr ctxt-var-decl (add-indices-to-ctxt is Γ') (data-functorₓ :: data-fmapₓ :: data-Muₓ :: data-muₓ :: data-castₓ :: data-Muₓᵣ :: data-muₓᵣ :: data-functor-indₓ :: [])
    --Γ = add-indices-to-ctxt is $ ctxt-var-decl data-functorₓ $ ctxt-var-decl data-fmapₓ $ ctxt-var-decl data-Muₓ $ ctxt-var-decl data-muₓ $ ctxt-var-decl data-castₓ $ ctxt-var-decl data-functor-indₓ Γ'
    namesₓ = record {
      data-functor = data-functorₓ;
      data-fmap = data-fmapₓ;
      data-Mu = data-Muₓᵣ;
      data-mu = data-muₓᵣ;
      data-cast = data-castₓᵣ;
      data-functor-ind = data-functor-indₓ;
      cast = castₓ;
      fixpoint-type = fixpoint-typeₓ;
      fixpoint-in = fixpoint-inₓ;
      fixpoint-out = fixpoint-outₓ;
      fixpoint-ind = fixpoint-indₓ;
      fixpoint-lambek = fixpoint-lambekₓ}
    
    new-var : ∀ {ℓ} {X : Set ℓ} → var → (var → X) → X
    new-var x f = f $ fresh-var x (ctxt-binds-var Γ) ρₓ

    functor-cmd = DefType pi-gen data-functorₓ (params-to-kind ps $ KndArrow k k) $
      params-to-tplams ps $
      TpLambda pi-gen pi-gen x (Tkk $ k) $
      indices-to-tplams is $
      new-var "x" λ xₓ → new-var "X" λ Xₓ →
      Iota pi-gen pi-gen xₓ (mtpeq id-term id-term) $
      Abs pi-gen Erased pi-gen Xₓ
        (Tkk $ indices-to-kind is $ KndTpArrow (mtpeq id-term id-term) star) $
      foldr (λ c → flip TpArrow NotErased $ mk-ctr-type Erased Γ c cs Xₓ)
        (TpAppt (indices-to-tpapps is $ mtpvar Xₓ) (mvar xₓ)) cs

    -- Note: had to set params to erased because args later in mu or mu' could be erased
    functor-ind-cmd = DefTerm pi-gen data-functor-indₓ NoType $
      params-to-lams ps $
      Lam pi-gen Erased pi-gen x (SomeClass $ Tkk k) $
      indices-to-lams is $
      new-var "x" λ xₓ → new-var "y" λ yₓ → new-var "e" λ eₓ → new-var "X" λ Xₓ →
      let T = indices-to-tpapps is $ TpApp (params-to-tpapps ps $ mtpvar data-functorₓ) (mtpvar x) in
      Lam pi-gen NotErased pi-gen xₓ (SomeClass $ Tkt T) $
      Lam pi-gen Erased pi-gen Xₓ
        (SomeClass $ Tkk $ indices-to-kind is $ KndTpArrow T star) $
      flip (foldr λ {c @ (Ctr _ x' _) → Lam pi-gen NotErased pi-gen x' $ SomeClass $
                                        Tkt $ mk-ctr-type NotErased Γ c cs Xₓ}) cs $
      flip mappe (Beta pi-gen NoTerm NoTerm) $
      flip mappe (mvar xₓ) $
      let Γ' = ctxt-var-decl xₓ $ ctxt-var-decl yₓ $ ctxt-var-decl eₓ $ ctxt-var-decl Xₓ Γ in
      flip (foldl λ {(Ctr _ x' T) → flip mapp $
                                  elim-pair (decompose-arrows Γ T) λ ps' Tₕ →
                                  params-to-lams' ps' $
                                  Mlam yₓ $ Mlam eₓ $
                                  params-to-apps ps' $ mvar x'}) cs $
      AppTp (IotaProj (mvar xₓ) "2" pi-gen) $
      indices-to-tplams is $
      TpLambda pi-gen pi-gen xₓ (Tkt $ mtpeq id-term id-term) $
      Abs pi-gen Erased pi-gen yₓ (Tkt T) $
      Abs pi-gen Erased pi-gen eₓ (Tkt $ mtpeq (mvar yₓ) (mvar xₓ)) $
      TpAppt (indices-to-tpapps is $ mtpvar Xₓ) $
      Phi pi-gen (mvar eₓ) (mvar yₓ) (mvar xₓ) pi-gen
    
    fmap-cmd : defTermOrType
    fmap-cmd with new-var "A" id | new-var "B" id | new-var "c" id
    ...| Aₓ | Bₓ | cₓ = DefTerm pi-gen data-fmapₓ (SomeType $
        params-to-alls ps $
        TpApp (params-to-tpapps ps $ mtpvar functorₓ) $
        params-to-tpapps ps $
        mtpvar data-functorₓ) $
      params-to-lams ps $
      Mlam Aₓ $ Mlam Bₓ $ Mlam cₓ $
      IotaPair pi-gen
        (indices-to-lams is $
         new-var "x" λ xₓ → mlam xₓ $
         IotaPair pi-gen (IotaProj (mvar xₓ) "1" pi-gen)
           (new-var "X" λ Xₓ → Mlam Xₓ $
             ctrs-to-lams' cs $
             foldl
               (flip mapp ∘ eta-expand-ctr)
               (AppTp (IotaProj (mvar xₓ) "2" pi-gen) $ mtpvar Xₓ) cs)
          NoGuide pi-gen)
        (Beta pi-gen NoTerm NoTerm) NoGuide pi-gen
      where
      eta-expand-ctr : ctr → term
      eta-expand-ctr (Ctr _ x' T) =
        mk-ctr-fmap-η+ (ctxt-var-decl Aₓ $ ctxt-var-decl Bₓ $ ctxt-var-decl cₓ Γ)
          (x , Aₓ , Bₓ , cₓ , params-to-apps (params-set-erased Erased ps) (mvar castₓ)) (mvar x') T

    type-cmd = DefType pi-gen x (params-to-kind ps k) $
      params-to-tplams ps $ TpAppt
        (TpApp (params-to-tpapps ps $ mtpvar fixpoint-typeₓ) $
          params-to-tpapps ps $ mtpvar data-functorₓ)
        (params-to-apps ps $ mvar data-fmapₓ)

    mu-proj : var → 𝔹 → type × (term → term)
    mu-proj Xₓ b =
      rename "i" from add-params-to-ctxt ps Γ for λ iₓ →
      let u = if b then id-term else params-to-apps (params-set-erased Erased ps) (mvar fixpoint-outₓ)
          Tₙ = λ T → Iota pi-gen pi-gen iₓ (indices-to-alls is $ TpArrow (indices-to-tpapps is $ mtpvar Xₓ) NotErased $ indices-to-tpapps is T) $ mtpeq (mvar iₓ) u
          T₁ = Tₙ $ params-to-tpapps ps $ mtpvar x
          T₂ = Tₙ $ TpApp (params-to-tpapps ps $ mtpvar data-functorₓ) $ mtpvar Xₓ
          T = if b then T₁ else T₂
          rₓ = if b then "c" else "o"
          t = λ mu → mapp (AppTp mu T) $ mlam "c" $ mlam "o" $ mvar rₓ in
      T , λ mu → Open pi-gen OpacTrans pi-gen data-Muₓ (Phi pi-gen (IotaProj (t mu) "2" pi-gen) (IotaProj (t mu) "1" pi-gen) u pi-gen)

    Mu-cmd = DefType pi-gen data-Muₓ (params-to-kind ps $ KndArrow k star) $
      params-to-tplams ps $
      rename "X" from add-params-to-ctxt ps Γ for λ Xₓ →
      rename "Y" from add-params-to-ctxt ps Γ for λ Yₓ →
      TpLambda pi-gen pi-gen Xₓ (Tkk k) $
      mall Yₓ (Tkk star) $
      flip (flip TpArrow NotErased) (mtpvar Yₓ) $
      TpArrow (fst $ mu-proj Xₓ tt) NotErased $
      TpArrow (fst $ mu-proj Xₓ ff) NotErased $
      mtpvar Yₓ

    mu-cmd = DefTerm pi-gen data-muₓ (SomeType $ params-to-alls (params-set-erased Erased ps) $ TpApp (params-to-tpapps ps $ mtpvar data-Muₓ) $ params-to-tpapps ps $ mtpvar x) $
      params-to-lams (params-set-erased Erased ps) $
      Open pi-gen OpacTrans pi-gen x $
      Open pi-gen OpacTrans pi-gen data-Muₓ $
      rename "Y" from add-params-to-ctxt ps Γ for λ Yₓ →
      rename "f" from add-params-to-ctxt ps Γ for λ fₓ →
      let pair = λ t → IotaPair pi-gen t (Beta pi-gen NoTerm (SomeTerm (erase t) pi-gen)) NoGuide pi-gen in
      Mlam Yₓ $ mlam fₓ $ mapp (mapp (mvar fₓ) $ pair $ indices-to-lams is $ id-term) $ pair $
        mappe (AppTp (params-to-apps (params-set-erased Erased ps) (mvar fixpoint-outₓ)) $ (params-to-tpapps ps $ mtpvar data-functorₓ)) (params-to-apps ps $ mvar data-fmapₓ)
    
    cast-cmd =
      rename "Y" from add-params-to-ctxt ps Γ for λ Yₓ →
      rename "mu" from add-params-to-ctxt ps Γ for λ muₓ →
      DefTerm pi-gen data-castₓ NoType $
      params-to-lams ps $
      Lam pi-gen Erased pi-gen Yₓ (SomeClass $ Tkk k) $
      Lam pi-gen Erased pi-gen muₓ (SomeClass $ Tkt $
        TpApp (params-to-tpapps ps $ mtpvar data-Muₓ) $ mtpvar Yₓ) $
      snd (mu-proj Yₓ tt) $ mvar muₓ

    ctr-cmd : ctr → defTermOrType
    ctr-cmd (Ctr _ x' T) with
        decompose-ctr-type Γ (subst Γ (params-to-tpapps ps $ mtpvar x) x T)
    ...| Tₕ , ps' , as' = DefTerm pi-gen x' NoType $
      Open pi-gen OpacTrans pi-gen x $
      params-to-lams ps $
      params-to-lams ps' $
      mapp (recompose-apps (ttys-to-args Erased $ drop (length ps) as') $
            mappe (AppTp (params-to-apps (params-set-erased Erased ps) $ mvar fixpoint-inₓ) $
              params-to-tpapps ps $ mtpvar data-functorₓ) $
        params-to-apps ps $ mvar data-fmapₓ) $
      rename "X" from add-params-to-ctxt ps' Γ for λ Xₓ →
      mk-ctr-term NotErased x' Xₓ cs ps'


{- Datatypes -}

ctxt-elab-ctr-def : var → params → type → (ctrs-length ctr-index : ℕ) → ctxt → ctxt
ctxt-elab-ctr-def c ps' t n i Γ@(mk-ctxt mod @ (fn , mn , ps , q) ss is os Δ) = mk-ctxt
  mod ss (trie-insert is ("//" ^ c) (ctr-def [] t n i (unerased-arrows $ abs-expand-type (ps ++ ps') t) , "missing" , "missing")) os Δ

ctxt-elab-ctrs-def : ctxt → params → ctrs → ctxt
ctxt-elab-ctrs-def Γ ps cs = foldr {B = ℕ → ctxt} (λ {(Ctr _ x T) Γ i → ctxt-elab-ctr-def x ps T (length cs) i $ Γ $ suc i}) (λ _ → Γ) cs 0


mendler-elab-mu-pure : ctxt → ctxt-datatype-info → encoded-datatype-names → maybe var → term → cases → maybe term
mendler-elab-mu-pure Γ (mk-data-info X is/X? asₚ asᵢ ps kᵢ k cs fcs) (mk-encoded-datatype-names _ _ _ _ _ _ _ _ fixpoint-inₓ fixpoint-outₓ fixpoint-indₓ fixpoint-lambekₓ) x? t ms =
  
  let ps-tm = id --λ t → foldr (const $ flip mapp id-term) t $ erase-params ps
      fix-ind = mvar fixpoint-indₓ -- hnf Γ unfold-all (ps-tm $ mvar fixpoint-indₓ) tt
      fix-out = mvar fixpoint-outₓ -- hnf Γ unfold-all (ps-tm $ mvar fixpoint-outₓ) tt
      μ-tm = λ x msf → mapp (mapp fix-ind t) $ mlam x $ rename "x" from ctxt-var-decl x Γ for λ fₓ → mlam fₓ $ msf $ mvar fₓ -- mapp fix-out $ mvar fₓ
      μ'-tm = λ msf → msf $ mapp fix-out t
      set-nth = λ l n a → foldr{B = maybe ℕ → 𝕃 (maybe term)}
        (λ {a' t nothing → a' :: t nothing;
            a' t (just zero) → a :: t nothing;
            a' t (just (suc n)) → a' :: t (just n)})
        (λ _ → []) l (just n) in
  -- Note: removing the implicit arguments below hangs Agda's type-checker!
  foldl{B = 𝕃 (maybe term) → maybe (term → term)}
    (λ c msf l → case_of_{B = maybe (term → term)} c
       λ {(Case _ x cas t) → env-lookup Γ ("//" ^ x) ≫=maybe
         λ {(ctr-def ps? _ n i a , _ , _) →
           msf (set-nth l i (just $ caseArgs-to-lams cas t)); _ → nothing}})
    (-- Note: lambda-expanding this "foldr..." also hangs Agda...?
     foldr (λ t? msf → msf ≫=maybe λ msf → t? ≫=maybe λ t →
              just λ t' → (msf (mapp t' t))) (just λ t → t))
    ms (map (λ _ → nothing) ms) ≫=maybe (just ∘ maybe-else' x? μ'-tm μ-tm)

mendler-elab-mu : elab-mu-t
mendler-elab-mu Γ (mk-data-info X is/X? asₚ asᵢ ps kᵢ k cs fcs)
  (mk-encoded-datatype-names
    data-functorₓ data-fmapₓ data-Muₓ data-muₓ data-castₓ data-functor-indₓ castₓ
    fixpoint-typeₓ fixpoint-inₓ fixpoint-outₓ fixpoint-indₓ fixpoint-lambekₓ)
   Xₒ x? t Tₘ ms =
  let infixl 10 _-is _-ps _`ps _·is _·ps
      _-is = recompose-apps $ ttys-to-args Erased asᵢ
      _`ps = recompose-apps asₚ
      _-ps = recompose-apps $ args-set-erased Erased asₚ
      _·is = recompose-tpapps asᵢ
      _·ps = recompose-tpapps $ args-to-ttys asₚ
      σ = fst (mk-inst ps (asₚ ++ ttys-to-args NotErased asᵢ))
      is = kind-to-indices Γ (substs Γ σ k)
      Γᵢₛ = add-indices-to-ctxt is $ add-params-to-ctxt ps Γ
      is-as : indices → args
      is-as = map λ {(Index x atk) →
        tk-elim atk (λ _ → TermArg Erased $ `vₓ x) (λ _ → TypeArg $ `Vₓ x)}
      is/X? = maybe-map `vₓ_ is/X? maybe-or either-else' x? (λ _ → nothing) (maybe-map fst)
      open? = Open pi-gen OpacTrans pi-gen X
      close? = Open pi-gen OpacOpaque pi-gen X
      ms' = foldr (λ {(Case _ x cas t) σ →
              let Γ' = add-caseArgs-to-ctxt cas Γᵢₛ in
              trie-insert σ x $ caseArgs-to-lams cas $
              rename "y" from Γ' for λ yₓ →
              rename "e" from Γ' for λ eₓ →
              `Λ yₓ ₊ `Λ eₓ ₊ close? (`ρ (`ς `vₓ eₓ) - t)}) empty-trie ms
      fmap = `vₓ data-fmapₓ `ps
      functor = `Vₓ data-functorₓ ·ps
      Xₜₚ = `Vₓ X ·ps
      in-fix = λ is/X? T asᵢ t → either-else' x? (λ x → recompose-apps asᵢ (`vₓ fixpoint-inₓ -ps · functor - fmap) ` (maybe-else' is/X? t λ is/X →
        recompose-apps asᵢ (`vₓ castₓ -ps - (fmap · T · Xₜₚ - (`open data-Muₓ - (is/X ` (`λ "to" ₊ `λ "out" ₊ `vₓ "to"))))) ` t)) (λ e → maybe-else' (is/X? maybe-or maybe-map fst e) t λ is/X → recompose-apps asᵢ (`vₓ castₓ -ps · `Vₓ Xₒ · Xₜₚ - (`open data-Muₓ - (is/X ` (`λ "to" ₊ `λ "out" ₊ `vₓ "to")))) ` t)
      app-lambek = λ is/X? t T asᵢ body → body - (in-fix is/X? T asᵢ t) -
        (recompose-apps asᵢ (`vₓ fixpoint-lambekₓ -ps · functor - fmap) ` (in-fix is/X? T asᵢ t)) in
  rename "x" from Γᵢₛ for λ xₓ →
  rename "y" from Γᵢₛ for λ yₓ →
  rename "y'" from ctxt-var-decl yₓ Γᵢₛ for λ y'ₓ →
  rename "z" from Γᵢₛ for λ zₓ →
  rename "e" from Γᵢₛ for λ eₓ →
  rename "X" from Γᵢₛ for λ Xₓ →
  foldl (λ {(Ctr _ x Tₓ) rec → rec ≫=maybe λ rec → trie-lookup ms' x ≫=maybe λ t →
    just λ tₕ → rec tₕ ` t}) (just λ t → t) cs ≫=maybe λ msf →
  just $ flip (either-else' x?)

    (λ _ → open? (app-lambek is/X? t (`Vₓ Xₒ ·ps) (ttys-to-args Erased asᵢ) (msf
      (let Tₛ = maybe-else' is/X? Xₜₚ λ _ → `Vₓ Xₒ
           fcₜ = maybe-else' is/X? id λ is/X → _`_ $ indices-to-apps is $
             `vₓ castₓ -ps · (functor ·ₜ Tₛ) · (functor ·ₜ Xₜₚ) -
               (fmap · Tₛ · Xₜₚ - (`open data-Muₓ - (is/X ` (`λ "to" ₊ `λ "out" ₊ `vₓ "to"))))
           out = maybe-else' is/X? (`vₓ fixpoint-outₓ -ps · functor - fmap) λ is/X →
             let i = `open data-Muₓ - is/X · (`ι xₓ :ₜ indices-to-alls is (indices-to-tpapps is Tₛ ➔ indices-to-tpapps is (functor ·ₜ Tₛ)) ₊ `[ `vₓ xₓ ≃ `vₓ fixpoint-outₓ ]) ` (`λ "to" ₊ `λ "out" ₊ `vₓ "out") in
             `φ i `₊2 - i `₊1 [ `vₓ fixpoint-outₓ ] in
      (`φ `β - (`vₓ data-functor-indₓ `ps · Tₛ -is ` (out -is ` t)) [ `vₓ fixpoint-outₓ ` erase t ])
        · (indices-to-tplams is $ `λₜ yₓ :ₜ indices-to-tpapps is (functor ·ₜ Tₛ) ₊
           `∀ y'ₓ :ₜ indices-to-tpapps is Xₜₚ ₊ `∀ eₓ :ₜ `[ `vₓ fixpoint-inₓ -ps ` `vₓ yₓ ≃ `vₓ y'ₓ ] ₊
           indices-to-tpapps is Tₘ `ₜ (`φ `vₓ eₓ -
             (indices-to-apps is (`vₓ fixpoint-inₓ -ps · functor - fmap) ` (fcₜ (`vₓ yₓ))) [ `vₓ y'ₓ ]))))) , Γ)

    λ xₒ → rename xₒ from Γᵢₛ for λ x →
    let Rₓₒ = mu-Type/ x
        isRₓₒ = mu-isType/ x in
    rename Rₓₒ from Γᵢₛ for λ Rₓ →
    rename isRₓₒ from Γᵢₛ for λ isRₓ →
    rename "to" from Γᵢₛ for λ toₓ →
    rename "out" from Γᵢₛ for λ outₓ →
    let fcₜ = `vₓ castₓ -ps · (functor ·ₜ `Vₓ Rₓ) · (functor ·ₜ Xₜₚ) - (fmap · `Vₓ Rₓ · Xₜₚ - `vₓ toₓ)
        subst-msf = subst-renamectxt Γᵢₛ (maybe-extract
          (renamectxt-insert* empty-renamectxt (xₒ :: isRₓₒ :: Rₓₒ :: toₓ :: outₓ :: xₓ :: yₓ :: y'ₓ :: []) (x :: isRₓ :: Rₓ :: toₓ :: outₓ :: xₓ :: yₓ :: y'ₓ :: [])) refl) ∘ msf in
    open? (`vₓ fixpoint-indₓ -ps · functor - fmap -is ` t · Tₘ `
      (`Λ Rₓ  ₊ `Λ toₓ ₊ `Λ outₓ ₊ `λ x ₊
       indices-to-lams is (`λ yₓ ₊
       `-[ isRₓ :ₜ `Vₓ data-Muₓ ·ps ·ₜ (`Vₓ Rₓ) `=
           `open data-Muₓ - (`Λ ignored-var ₊ `λ xₓ ₊ `vₓ xₓ ` (`vₓ toₓ) ` (`vₓ outₓ))]-
       (app-lambek (just $ `vₓ isRₓ) (`vₓ yₓ) (`Vₓ Rₓ) (is-as is) $ subst-msf
         ((`φ `β - (indices-to-apps is (`vₓ data-functor-indₓ `ps · (`Vₓ Rₓ)) ` `vₓ yₓ) [ `vₓ yₓ ]) ·
           (indices-to-tplams is $ `λₜ yₓ :ₜ indices-to-tpapps is functor ·ₜ (`Vₓ Rₓ) ₊
             `∀ y'ₓ :ₜ indices-to-tpapps is Xₜₚ ₊ `∀ eₓ :ₜ `[ `vₓ fixpoint-inₓ -ps ` `vₓ yₓ ≃ `vₓ y'ₓ ] ₊
             indices-to-tpapps is Tₘ `ₜ (`φ `vₓ eₓ -
               (`vₓ fixpoint-inₓ -ps · functor - fmap ` (indices-to-apps is fcₜ ` (`vₓ yₓ)))
               [ `vₓ y'ₓ ]))))))) , ctxt-datatype-decl' X isRₓ Rₓ asₚ Γ


mendler-encoding : datatype-encoding
mendler-encoding =
  record {
    template = templateMendler;
    functor = "Functor";
    cast = "cast";
    fixpoint-type = "CVFixIndM";
    fixpoint-in = "cvInFixIndM";
    fixpoint-out = "cvOutFixIndM";
    fixpoint-ind = "cvIndFixIndM";
    fixpoint-lambek = "lambek";
    elab-mu = mendler-elab-mu;
    elab-mu-pure = mendler-elab-mu-pure
  }

mendler-simple-encoding : datatype-encoding
mendler-simple-encoding =
  record {
    template = templateMendlerSimple;
    functor = "RecFunctor";
    cast = "cast";
    fixpoint-type = "FixM";
    fixpoint-out = "outFix";
    fixpoint-in = "inFix";
    fixpoint-ind = "IndFixM";
    fixpoint-lambek = "lambek";
    elab-mu = mendler-elab-mu;
    elab-mu-pure = mendler-elab-mu-pure
  }

selected-encoding = case cedille-options.options.datatype-encoding options of λ where
  cedille-options.Mendler → mendler-simple-encoding
  cedille-options.Mendler-old → mendler-encoding
