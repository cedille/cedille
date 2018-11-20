{-# OPTIONS --allow-unsolved-metas #-}
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

uncurry' : ∀ {A B C D : Set} → (A → B → C → D) → (A × B × C) → D
uncurry' f (a , b , c) = f a b c

uncurry'' : ∀ {A B C D E : Set} → (A → B → C → D → E) → (A × B × C × D) → E
uncurry'' f (a , b , c , d) = f a b c d

uncurry''' : ∀ {A B C D E F : Set} → (A → B → C → D → E → F) → (A × B × C × D × E) → F
uncurry''' f (a , b , c , d , e) = f a b c d e

ctxt-term-decl' : posinfo → var → type → ctxt → ctxt
ctxt-term-decl' pi x T (mk-ctxt (fn , mn , ps , q) ss is os) =
  mk-ctxt (fn , mn , ps , trie-insert q x (x , [])) ss
    (trie-insert is x (term-decl T , fn , pi)) os

ctxt-type-decl' : posinfo → var → kind → ctxt → ctxt
ctxt-type-decl' pi x k (mk-ctxt (fn , mn , ps , q) ss is os) =
  mk-ctxt (fn , mn , ps , trie-insert q x (x , [])) ss
    (trie-insert is x (type-decl k , fn , pi)) os

ctxt-tk-decl' : posinfo → var → tk → ctxt → ctxt
ctxt-tk-decl' pi x (Tkt T) = ctxt-term-decl' pi x T
ctxt-tk-decl' pi x (Tkk k) = ctxt-type-decl' pi x k

ctxt-param-decl : var → var → tk → ctxt → ctxt
ctxt-param-decl x x' atk Γ @ (mk-ctxt (fn , mn , ps , q) ss is os) =
  let d = case atk of λ {(Tkt T) → term-decl T; (Tkk k) → type-decl k} in
  mk-ctxt
  (fn , mn , ps , trie-insert q x (x , [])) ss
  (trie-insert is x' (d , fn , pi-gen)) os

ctxt-term-def' : var → var → term → type → opacity → ctxt → ctxt
ctxt-term-def' x x' t T op Γ @ (mk-ctxt (fn , mn , ps , q) ss is os) = mk-ctxt
  (fn , mn , ps , qualif-insert-params q (mn # x) x ps) ss
  (trie-insert is x' (term-def (just ps) op (hnf Γ unfold-head t tt) T , fn , x)) os

ctxt-type-def' : var → var → type → kind → opacity → ctxt → ctxt
ctxt-type-def' x x' T k op Γ @ (mk-ctxt (fn , mn , ps , q) ss is os) = mk-ctxt
  (fn , mn , ps , qualif-insert-params q (mn # x) x ps) ss
  (trie-insert is x' (type-def (just ps) op (hnf Γ (unfolding-elab unfold-head) T tt) k , fn , x)) os

ctxt-let-term-def : posinfo → var → term → type → ctxt → ctxt
ctxt-let-term-def pi x t T (mk-ctxt (fn , mn , ps , q) ss is os) =
  mk-ctxt (fn , mn , ps , trie-insert q x (x , [])) ss
    (trie-insert is x (term-def nothing OpacTrans t T , fn , pi)) os

ctxt-let-type-def : posinfo → var → type → kind → ctxt → ctxt
ctxt-let-type-def pi x T k (mk-ctxt (fn , mn , ps , q) ss is os) =
  mk-ctxt (fn , mn , ps , trie-insert q x (x , [])) ss
    (trie-insert is x (type-def nothing OpacTrans T k , fn , pi)) os

ctxt-μ-out-def : var → term → var → ctxt → ctxt
ctxt-μ-out-def x t y (mk-ctxt mod ss is os) = mk-ctxt mod ss
  (trie-insert is x (term-udef nothing OpacTrans t , y , y)) os

ctxt-kind-def' : var → var → params → kind → ctxt → ctxt
ctxt-kind-def' x x' ps2 k Γ @ (mk-ctxt (fn , mn , ps1 , q) ss is os) = mk-ctxt
  (fn , mn , ps1 , qualif-insert-params q (mn # x) x ps1) ss
  (trie-insert is x' (kind-def (ps1 ++ qualif-params Γ ps2) k' , fn , pi-gen)) os
  where
  k' = hnf Γ (unfolding-elab unfold-head) k tt

ctxt-datatype-def' : var → var → defParams → kind → kind → ctrs → ctxt → ctxt
ctxt-datatype-def' x x' psᵢ kᵢ k cs Γ@(mk-ctxt (fn , mn , ps , q) ss is os) = mk-ctxt
  (fn , mn , ps , q') ss
  (trie-insert is x' (datatype-def (maybe-map (ps ++_) psᵢ) kᵢ k cs , fn , x)) os
  where
  q' = qualif-insert-params q x x' (maybe-else [] (λ _ → ps) psᵢ)

ctxt-lookup-term-var' : ctxt → var → maybe type
ctxt-lookup-term-var' Γ @ (mk-ctxt (fn , mn , ps , q) ss is os) x =
  env-lookup Γ x ≫=maybe λ where
    (term-decl T , _) → just T
    (term-def ps _ _ T , _ , x') →
      let ps = maybe-else [] id ps in
      just $ abs-expand-type ps T
    _ → nothing

-- TODO: Could there be parameter/argument clashes if the same parameter variable is defined multiple times?
-- TODO: Could variables be parameter-expanded multiple times?
ctxt-lookup-type-var' : ctxt → var → maybe kind
ctxt-lookup-type-var' Γ @ (mk-ctxt (fn , mn , ps , q) ss is os) x =
  env-lookup Γ x ≫=maybe λ where
    (type-decl k , _) → just k
    (type-def ps _ _ k , _ , x') →
      let ps = maybe-else [] id ps in
      just $ abs-expand-kind ps k
    _ → nothing

subst-qualif : ∀ {ed : exprd} → ctxt → renamectxt → ⟦ ed ⟧ → ⟦ ed ⟧
subst-qualif{TERM} Γ ρ = subst-renamectxt Γ ρ ∘ qualif-term Γ
subst-qualif{TYPE} Γ ρ = subst-renamectxt Γ ρ ∘ qualif-type Γ
subst-qualif{KIND} Γ ρ = subst-renamectxt Γ ρ ∘ qualif-kind Γ
subst-qualif Γ ρ = id

rename-validify : string → string
rename-validify = 𝕃char-to-string ∘ (h ∘ string-to-𝕃char) where
  validify-char : char → 𝕃 char
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
get-renaming ρ xₒ x = let x' = fresh-var' x (renamectxt-in-range ρ) ρ in x' , renamectxt-insert ρ xₒ x'

rename_-_from_for_ : ∀ {X : Set} → var → var → renamectxt → (var → renamectxt → X) → X
rename xₒ - "_" from ρ for f = f "_" ρ
rename xₒ - x from ρ for f = uncurry f $ get-renaming ρ xₒ x

rename_-_lookup_for_ : ∀ {X : Set} → var → var → renamectxt → (var → renamectxt → X) → X
rename xₒ - x lookup ρ for f with renamectxt-lookup ρ xₒ
...| nothing = rename xₒ - x from ρ for f
...| just x' = f x' ρ

qualif-new-var : ctxt → var → var
qualif-new-var Γ x = ctxt-get-current-modname Γ # x

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
  reindex-fresh-var ρ is "_" = "_"
  reindex-fresh-var ρ is x =
    fresh-var x (λ x' → ctxt-binds-var Γ x' || trie-contains is x') ρ

  rename-indices : renamectxt → trie indices → indices
  rename-indices ρ is = foldr {B = renamectxt → indices}
    (λ {(Index x atk) f ρ →
       let x' = reindex-fresh-var ρ is x in
       Index x' (substh-tk {TERM} Γ ρ empty-trie atk) :: f (renamectxt-insert ρ x x')})
    (λ ρ → []) isₒ ρ
  
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
  reindex       = λ ρ is x → x

  rc-is : renamectxt → indices → renamectxt
  rc-is = foldr λ {(Index x atk) ρ → renamectxt-insert ρ x x}
  
  index-var = "indices"
  index-type-var = "Indices"
  is-index-var = isJust ∘ is-pfx index-var
  is-index-type-var = isJust ∘ is-pfx index-type-var
  
  reindex-term ρ is (App t me (Var pi x)) with trie-lookup is x
  ...| nothing = App (reindex-term ρ is t) me (reindex-term ρ is (Var pi x))
  ...| just is' = indices-to-apps is' $ reindex-term ρ is t
  reindex-term ρ is (App t me t') =
    App (reindex-term ρ is t) me (reindex-term ρ is t')
  reindex-term ρ is (AppTp t T) =
    AppTp (reindex-term ρ is t) (reindex-type ρ is T)
  reindex-term ρ is (Beta pi ot ot') =
    Beta pi (reindex-optTerm ρ is ot) (reindex-optTerm ρ is ot')
  reindex-term ρ is (Chi pi oT t) =
    Chi pi (reindex-optType ρ is oT) (reindex-term ρ is t)
  reindex-term ρ is (Delta pi oT t) =
    Delta pi (reindex-optType ρ is oT) (reindex-term ρ is t)
  reindex-term ρ is (Epsilon pi lr m t) =
    Epsilon pi lr m (reindex-term ρ is t)
  reindex-term ρ is (Hole pi) =
    Hole pi
  reindex-term ρ is (IotaPair pi t t' g pi') =
    IotaPair pi (reindex-term ρ is t) (reindex-term ρ is t') (reindex-optGuide ρ is g) pi'
  reindex-term ρ is (IotaProj t n pi) =
    IotaProj (reindex-term ρ is t) n pi
  reindex-term ρ is (Lam pi me pi' x oc t) with is-index-var x
  ...| ff = let x' = reindex-fresh-var ρ is x in
    Lam pi me pi' x' (reindex-optClass ρ is oc) (reindex-term (renamectxt-insert ρ x x') is t)
  ...| tt with rename-indices ρ is | oc
  ...| isₙ | NoClass = indices-to-lams' isₙ $ reindex-term (rc-is ρ isₙ) (trie-insert is x isₙ) t
  ...| isₙ | SomeClass atk = indices-to-lams isₙ $ reindex-term (rc-is ρ isₙ) (trie-insert is x isₙ) t
  reindex-term ρ is (Let pi d t) =
    elim-pair (reindex-defTermOrType ρ is d) λ d' ρ' → Let pi d' (reindex-term ρ' is t)
  reindex-term ρ is (Open pi x t) =
    Open pi x (reindex-term ρ is t)
  reindex-term ρ is (Parens pi t pi') =
    reindex-term ρ is t
  reindex-term ρ is (Phi pi t₌ t₁ t₂ pi') =
    Phi pi (reindex-term ρ is t₌) (reindex-term ρ is t₁) (reindex-term ρ is t₂) pi'
  reindex-term ρ is (Rho pi op on t og t') =
    Rho pi op on (reindex-term ρ is t) (reindex-optGuide ρ is og) (reindex-term ρ is t')
  reindex-term ρ is (Sigma pi t) =
    Sigma pi (reindex-term ρ is t)
  reindex-term ρ is (Theta pi θ t ts) =
    Theta pi (reindex-theta ρ is θ) (reindex-term ρ is t) (reindex-lterms ρ is ts)
  reindex-term ρ is (Var pi x) =
    Var pi $ renamectxt-rep ρ x
  reindex-term ρ is (Mu pi pi' x t oT pi'' cs pi''') = Var pi-gen "template-mu-not-allowed"
  reindex-term ρ is (Mu' pi t oT pi' cs pi'') = Var pi-gen "template-mu-not-allowed" 
  
  reindex-type ρ is (Abs pi me pi' x atk T) with is-index-var x
  ...| ff = let x' = reindex-fresh-var ρ is x in
    Abs pi me pi' x' (reindex-tk ρ is atk) (reindex-type (renamectxt-insert ρ x x') is T)
  ...| tt = let isₙ = rename-indices ρ is in
    indices-to-alls isₙ $ reindex-type (rc-is ρ isₙ) (trie-insert is x isₙ) T
  reindex-type ρ is (Iota pi pi' x T T') =
    let x' = reindex-fresh-var ρ is x in
    Iota pi pi' x' (reindex-type ρ is T) (reindex-type (renamectxt-insert ρ x x') is T')
  reindex-type ρ is (Lft pi pi' x t lT) =
    let x' = reindex-fresh-var ρ is x in
    Lft pi pi' x' (reindex-term (renamectxt-insert ρ x x') is t) (reindex-liftingType ρ is lT)
  reindex-type ρ is (NoSpans T pi) =
    NoSpans (reindex-type ρ is T) pi
  reindex-type ρ is (TpLet pi d T) =
    elim-pair (reindex-defTermOrType ρ is d) λ d' ρ' → TpLet pi d' (reindex-type ρ' is T)
  reindex-type ρ is (TpApp T T') =
    TpApp (reindex-type ρ is T) (reindex-type ρ is T')
  reindex-type ρ is (TpAppt T (Var pi x)) with trie-lookup is x
  ...| nothing = TpAppt (reindex-type ρ is T) (reindex-term ρ is (Var pi x))
  ...| just is' = indices-to-tpapps is' $ reindex-type ρ is T
  reindex-type ρ is (TpAppt T t) =
    TpAppt (reindex-type ρ is T) (reindex-term ρ is t)
  reindex-type ρ is (TpArrow (TpVar pi x) Erased T) with is-index-type-var x
  ...| ff = TpArrow (reindex-type ρ is (TpVar pi x)) Erased (reindex-type ρ is T)
  ...| tt = let isₙ = rename-indices ρ is in
    indices-to-alls isₙ $ reindex-type (rc-is ρ isₙ) (trie-insert is x isₙ) T
  reindex-type ρ is (TpArrow T me T') =
    TpArrow (reindex-type ρ is T) me (reindex-type ρ is T')
  reindex-type ρ is (TpEq pi t t' pi') =
    TpEq pi (reindex-term ρ is t) (reindex-term ρ is t') pi'
  reindex-type ρ is (TpHole pi) =
    TpHole pi
  reindex-type ρ is (TpLambda pi pi' x atk T) with is-index-var x
  ...| ff = let x' = reindex-fresh-var ρ is x in
    TpLambda pi pi' x' (reindex-tk ρ is atk) (reindex-type (renamectxt-insert ρ x x') is T)
  ...| tt = let isₙ = rename-indices ρ is in
    indices-to-tplams isₙ $ reindex-type (rc-is ρ isₙ) (trie-insert is x isₙ) T
  reindex-type ρ is (TpParens pi T pi') =
    reindex-type ρ is T
  reindex-type ρ is (TpVar pi x) =
    TpVar pi $ renamectxt-rep ρ x
  
  reindex-kind ρ is (KndParens pi k pi') =
    reindex-kind ρ is k
  reindex-kind ρ is (KndArrow k k') =
    KndArrow (reindex-kind ρ is k) (reindex-kind ρ is k')
  reindex-kind ρ is (KndPi pi pi' x atk k) with is-index-var x
  ...| ff = let x' = reindex-fresh-var ρ is x in
    KndPi pi pi' x' (reindex-tk ρ is atk) (reindex-kind (renamectxt-insert ρ x x') is k)
  ...| tt = let isₙ = rename-indices ρ is in
    indices-to-kind isₙ $ reindex-kind (rc-is ρ isₙ) (trie-insert is x isₙ) k
  reindex-kind ρ is (KndTpArrow (TpVar pi x) k) with is-index-type-var x
  ...| ff = KndTpArrow (reindex-type ρ is (TpVar pi x)) (reindex-kind ρ is k)
  ...| tt = let isₙ = rename-indices ρ is in
    indices-to-kind isₙ $ reindex-kind (rc-is ρ isₙ) is k
  reindex-kind ρ is (KndTpArrow T k) =
    KndTpArrow (reindex-type ρ is T) (reindex-kind ρ is k)
  reindex-kind ρ is (KndVar pi x as) =
    KndVar pi (renamectxt-rep ρ x) (reindex-args ρ is as)
  reindex-kind ρ is (Star pi) =
    Star pi
  
  reindex-tk ρ is (Tkt T) = Tkt $ reindex-type ρ is T
  reindex-tk ρ is (Tkk k) = Tkk $ reindex-kind ρ is k
  
  -- Can't reindex large indices in a lifting type (LiftPi requires a type, not a tk),
  -- so for now we will just ignore reindexing lifting types.
  -- Types withing lifting types will still be reindexed, though.
  reindex-liftingType ρ is (LiftArrow lT lT') =
    LiftArrow (reindex-liftingType ρ is lT) (reindex-liftingType ρ is lT')
  reindex-liftingType ρ is (LiftParens pi lT pi') =
    reindex-liftingType ρ is lT
  reindex-liftingType ρ is (LiftPi pi x T lT) =
    let x' = reindex-fresh-var ρ is x in
    LiftPi pi x' (reindex-type ρ is T) (reindex-liftingType (renamectxt-insert ρ x x') is lT)
  reindex-liftingType ρ is (LiftStar pi) =
    LiftStar pi
  reindex-liftingType ρ is (LiftTpArrow T lT) =
    LiftTpArrow (reindex-type ρ is T) (reindex-liftingType ρ is lT)
  
  reindex-optTerm ρ is NoTerm = NoTerm
  reindex-optTerm ρ is (SomeTerm t pi) = SomeTerm (reindex-term ρ is t) pi
  
  reindex-optType ρ is NoType = NoType
  reindex-optType ρ is (SomeType T) = SomeType (reindex-type ρ is T)
  
  reindex-optClass ρ is NoClass = NoClass
  reindex-optClass ρ is (SomeClass atk) = SomeClass (reindex-tk ρ is atk)
  
  reindex-optGuide ρ is NoGuide = NoGuide
  reindex-optGuide ρ is (Guide pi x T) =
    let x' = reindex-fresh-var ρ is x in
    Guide pi x' (reindex-type (renamectxt-insert ρ x x') is T)
  
  reindex-lterms ρ is = map λ where
    (Lterm me t) → Lterm me (reindex-term ρ is t)

  reindex-theta ρ is (AbstractVars xs) = maybe-else Abstract AbstractVars $ reindex-vars ρ is $ just xs
  reindex-theta ρ is θ = θ

  reindex-vars''' : vars → vars → vars
  reindex-vars''' (VarsNext x xs) xs' = VarsNext x $ reindex-vars''' xs xs'
  reindex-vars''' (VarsStart x) xs = VarsNext x xs
  reindex-vars'' : vars → maybe vars
  reindex-vars'' (VarsNext x (VarsStart x')) = just $ VarsStart x
  reindex-vars'' (VarsNext x xs) = maybe-map (VarsNext x) $ reindex-vars'' xs
  reindex-vars'' (VarsStart x) = nothing
  reindex-vars' : renamectxt → trie indices → var → maybe vars
  reindex-vars' ρ is x = maybe-else (just $ VarsStart $ renamectxt-rep ρ x)
    (reindex-vars'' ∘ flip foldr (VarsStart "") λ {(Index x atk) → VarsNext x}) (trie-lookup is x)
  reindex-vars ρ is (just (VarsStart x)) = reindex-vars' ρ is x
  reindex-vars ρ is (just (VarsNext x xs)) = maybe-else (reindex-vars ρ is $ just xs)
    (λ xs' → maybe-map (reindex-vars''' xs') $ reindex-vars ρ is $ just xs) $ reindex-vars' ρ is x
  reindex-vars ρ is nothing = nothing
  
  reindex-arg ρ is (TermArg me t) = TermArg me (reindex-term ρ is t)
  reindex-arg ρ is (TypeArg T) = TypeArg (reindex-type ρ is T)
  reindex-args ρ is = map(reindex-arg ρ is)
  
  reindex-defTermOrType ρ is (DefTerm pi x oT t) =
    let x' = reindex-fresh-var ρ is x in
    DefTerm pi x' (reindex-optType ρ is oT) (reindex-term ρ is t) , renamectxt-insert ρ x x'
  reindex-defTermOrType ρ is (DefType pi x k T) =
    let x' = reindex-fresh-var ρ is x in
    DefType pi x' (reindex-kind ρ is k) (reindex-type ρ is T) , renamectxt-insert ρ x x'

  reindex-cmds : renamectxt → trie indices → cmds → cmds × renamectxt
  reindex-cmds ρ is [] = [] , ρ
  reindex-cmds ρ is ((ImportCmd i) :: cs) =
    elim-pair (reindex-cmds ρ is cs) $ _,_ ∘ _::_ (ImportCmd i)
  reindex-cmds ρ is ((DefTermOrType op d pi) :: cs) =
    elim-pair (reindex-defTermOrType ρ is d) λ d' ρ' →
    elim-pair (reindex-cmds ρ' is cs) $ _,_ ∘ _::_ (DefTermOrType op d' pi)
  reindex-cmds ρ is ((DefKind pi x ps k pi') :: cs) =
    let x' = reindex-fresh-var ρ is x in
    elim-pair (reindex-cmds (renamectxt-insert ρ x x') is cs) $ _,_ ∘ _::_
      (DefKind pi x' ps (reindex-kind ρ is k) pi')
  reindex-cmds ρ is ((DefDatatype dt pi) :: cs) =
    reindex-cmds ρ is cs -- Templates can't use datatypes!

reindex-file : ctxt → indices → start → cmds × renamectxt
reindex-file Γ is (File csᵢ pi' pi'' x ps cs pi''') =
  reindex-cmds empty-renamectxt empty-trie cs
  where open reindexing Γ is


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

record encoded-datatype-names : Set where
  constructor mk-encoded-datatype-names
  field
    data-functor : var
    data-fmap : var
    data-functor-ind : var
    cast : var
    fixpoint-type : var
    fixpoint-in : var
    fixpoint-out : var
    fixpoint-ind : var

elab-mu-t : Set
elab-mu-t = ctxt → datatype → encoded-datatype-names → var → maybe var → term → type → args → cases → maybe (term × ctxt)

elab-mu-prev-name = "///prev"

record encoded-datatype : Set where
  constructor mk-encoded-datatype
  field
    data-def : datatype
    names : encoded-datatype-names
    elab-mu : elab-mu-t
    elab-mu-pure : ctxt → params → encoded-datatype-names → maybe var → term → cases → maybe term

  check-mu : ctxt → var → maybe var → term → optType → cases → args → type → maybe (term × ctxt)
  check-mu Γ Xₒ x? t oT ms as T with data-def
  check-mu Γ Xₒ x? t oT ms as T | Data X ps is cs
    with kind-to-indices Γ (indices-to-kind is star) | oT
  check-mu Γ Xₒ x? t oT ms as T | Data X ps _ cs | is | NoType =
    elab-mu Γ (Data X ps is cs) names Xₒ x? t
      (indices-to-tplams is $ TpLambda pi-gen pi-gen ignored-var
        (Tkt $ indices-to-tpapps is $
          recompose-tpapps (args-to-ttys $ take (length ps) as) $ mtpvar X) T) as ms
  check-mu Γ Xₒ x? t oT ms as T | Data X ps _ cs | is | SomeType Tₘ =
    elab-mu Γ (Data X ps is cs) names Xₒ x? t Tₘ as ms

  synth-mu : ctxt → var → maybe var → term → optType → cases → args → maybe (term × ctxt)
  synth-mu Γ Xₒ x? t NoType _ as = nothing
  synth-mu Γ Xₒ x? t (SomeType Tₘ) ms as = elab-mu Γ data-def names Xₒ x? t Tₘ as ms

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
    elab-mu : elab-mu-t
    elab-mu-pure : ctxt → params → encoded-datatype-names → maybe var → term → cases → maybe term

  mk-defs : ctxt → datatype → cmds × encoded-datatype
  mk-defs Γ'' (Data x ps is cs) =
    tcs ++
    (csn OpacTrans functor-cmd $
     csn OpacTrans functor-ind-cmd $
     csn OpacTrans fmap-cmd $
     csn OpacOpaque type-cmd $
     foldr (csn OpacTrans ∘ ctr-cmd) [] cs) ,
    record {
      elab-mu = elab-mu;
      elab-mu-pure = elab-mu-pure;
      data-def = Data x ps is cs;
      names = namesₓ}
    where
    csn : opacity → defTermOrType → cmds → cmds
    csn o d = DefTermOrType o d pi-gen ::_

    k = indices-to-kind is $ Star pi-gen
    
    Γ' = add-params-to-ctxt ps $ add-ctrs-to-ctxt cs $ ctxt-var-decl x Γ''
    
    tcs-ρ = reindex-file Γ' is template
    tcs = fst tcs-ρ
    ρ = snd tcs-ρ

    data-functorₓ = fresh-var (x ^ "F") (ctxt-binds-var Γ') ρ
    data-fmapₓ = fresh-var (x ^ "Fmap") (ctxt-binds-var Γ') ρ
    data-functor-indₓ = fresh-var (x ^ "IndF") (ctxt-binds-var Γ') ρ
    functorₓ = renamectxt-rep ρ functor
    castₓ = renamectxt-rep ρ cast
    fixpoint-typeₓ = renamectxt-rep ρ fixpoint-type
    fixpoint-inₓ = renamectxt-rep ρ fixpoint-in
    fixpoint-outₓ = renamectxt-rep ρ fixpoint-out
    fixpoint-indₓ = renamectxt-rep ρ fixpoint-ind
    Γ = add-indices-to-ctxt is $ ctxt-var-decl data-functorₓ $ ctxt-var-decl data-fmapₓ $ ctxt-var-decl data-functor-indₓ Γ'
    namesₓ = record {
      data-functor = data-functorₓ;
      data-fmap = data-fmapₓ;
      data-functor-ind = data-functor-indₓ;
      cast = castₓ;
      fixpoint-type = fixpoint-typeₓ;
      fixpoint-in = fixpoint-inₓ;
      fixpoint-out = fixpoint-outₓ;
      fixpoint-ind = fixpoint-indₓ}
    
    new-var : ∀ {ℓ} {X : Set ℓ} → var → (var → X) → X
    new-var x f = f $ fresh-var x (ctxt-binds-var Γ) ρ

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
        TpApp (mtpvar functorₓ) $
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
               (flip mapp ∘ eta-expand-fmap)
               (AppTp (IotaProj (mvar xₓ) "2" pi-gen) $ mtpvar Xₓ) cs)
          NoGuide pi-gen)
        (Beta pi-gen NoTerm NoTerm) NoGuide pi-gen
      where
      eta-expand-fmaph-type : ctxt → var → type → term
      eta-expand-fmaph-type Γ x' T with decompose-ctr-type Γ T
      ...| Tₕ , ps , as with add-params-to-ctxt ps Γ
      ...| Γ' =
        params-to-lams' ps $
        flip mapp (params-to-apps ps $ mvar x') $
        recompose-apps (ttys-to-args Erased as) $
        flip mappe (mvar cₓ) $
        flip AppTp (mtpvar Bₓ) $
        AppTp (mvar castₓ) (mtpvar Aₓ)

      eta-expand-fmap : ctr → term
      eta-expand-fmap (Ctr _ x' T) with
        ctxt-var-decl Aₓ $ ctxt-var-decl Bₓ $ ctxt-var-decl cₓ Γ
      ...| Γ' with decompose-ctr-type Γ' T
      ...| Tₕ , ps , as with foldr (λ {(Decl _ _ _ x'' _ _) → ctxt-var-decl x''}) Γ' ps
      ...| Γ'' = params-to-lams' ps $ foldl
        (λ {(Decl pi pi' me x'' (Tkt T) pi'') t → App t me $
              if ~ is-free-in tt x T then mvar x'' else eta-expand-fmaph-type Γ'' x'' T;
            (Decl pi pi' me x'' (Tkk k) pi'') t → AppTp t $ mtpvar x''})
        (mvar x') $ ps

    type-cmd = DefType pi-gen x (params-to-kind ps $ k) $
      params-to-tplams ps $ TpAppt
        (TpApp (mtpvar fixpoint-typeₓ) $ params-to-tpapps ps $ mtpvar data-functorₓ)
        (params-to-apps ps $ mvar data-fmapₓ)

    ctr-cmd : ctr → defTermOrType
    ctr-cmd (Ctr _ x' T) with
        decompose-ctr-type Γ (subst Γ (params-to-tpapps ps $ mtpvar x) x T)
    ...| Tₕ , ps' , as' = DefTerm pi-gen x' NoType $
      params-to-lams ps $
      params-to-lams ps' $
      mapp (recompose-apps (ttys-to-args Erased $ drop (length ps) as') $
            mappe (AppTp (mvar fixpoint-inₓ) $
              params-to-tpapps ps $ mtpvar data-functorₓ) $
        params-to-apps ps $ mvar data-fmapₓ) $
      rename "X" from add-params-to-ctxt ps' Γ for λ Xₓ →
      mk-ctr-term NotErased x' Xₓ cs ps'




{- Datatypes -}

ctxt-elab-ctr-def : var → type → (ctrs-length ctr-index : ℕ) → ctxt → ctxt
ctxt-elab-ctr-def c t n i Γ@(mk-ctxt mod @ (fn , mn , ps , q) ss is os) = mk-ctxt
  mod ss (trie-insert is ("//" ^ c) (ctr-def (just ps) t n i (unerased-arrows t) , "missing" , "missing")) os

ctxt-elab-ctrs-def : ctxt → ctrs → ctxt
ctxt-elab-ctrs-def Γ cs = foldr {B = ℕ → ctxt} (λ {(Ctr _ x T) Γ i → ctxt-elab-ctr-def x T (length cs) i $ Γ $ suc i}) (λ _ → Γ) cs 0

mendler-elab-mu-pure : ctxt → params → encoded-datatype-names → maybe var → term → cases → maybe term
mendler-elab-mu-pure Γ ps (mk-encoded-datatype-names _ _ _ _ _ fixpoint-inₓ fixpoint-outₓ fixpoint-indₓ) x? t ms =
  let ps-tm = λ t → foldr (const $ flip mapp id-term) t $ erase-params ps
      fix-ind = hnf Γ unfold-all (ps-tm $ mvar fixpoint-indₓ) tt
      fix-out = hnf Γ unfold-all (ps-tm $ mvar fixpoint-outₓ) tt
      μ-tm = λ x msf → mapp (mapp fix-ind t) $ mlam x $ rename "x" from ctxt-var-decl x Γ for λ fₓ → mlam fₓ $ msf $ mapp fix-out $ mvar fₓ
      μ'-tm = λ msf → msf t
      set-nth = λ l n a → foldr {B = maybe ℕ → 𝕃 (maybe term)} (λ {a' t nothing → a' :: t nothing; a' t (just zero) → a :: t nothing; a' t (just (suc n)) → a' :: t (just n)}) (λ _ → []) l (just n) in
  foldl (λ {(Case _ x cas t) msf l → env-lookup Γ ("//" ^ x) ≫=maybe λ {(ctr-def ps? _ n i a , _ , _) → msf $ set-nth l i (just $ caseArgs-to-lams (drop (maybe-else' ps? 0 length) cas) t); _ → nothing}}) (λ l → foldl (λ t? msf → msf ≫=maybe λ msf → t? ≫=maybe λ t → just λ t' → (msf (mapp t' t))) (just λ t → t) l) ms (foldr (λ _ → nothing ::_) [] ms) ≫=maybe (just ∘ maybe-else' x? μ'-tm μ-tm)

mendler-elab-mu : elab-mu-t
mendler-elab-mu Γ (Data X ps is cs) (mk-encoded-datatype-names data-functorₓ data-fmapₓ data-functor-indₓ castₓ fixpoint-typeₓ fixpoint-inₓ fixpoint-outₓ fixpoint-indₓ) Xₒ x? t Tₘ as ms =
  let len-psₜ = length as ∸ length is
      len-psₙ = length ps
      len-psₘ = len-psₜ ∸ len-psₙ
      asᵢ = drop len-psₜ as
      asₜ = take len-psₜ as
      asₚ = drop len-psₘ (take len-psₜ as)
      σ = fst (mk-inst ps asₚ)
      is = map (λ {(Index x atk) → Index x (substs Γ σ atk)}) is
      ms' = foldr (λ {(Case _ x cas t) σ →
              trie-insert σ x $ caseArgs-to-lams (drop len-psₙ cas) t}) empty-trie ms
      as-ttys = map λ {(TermArg _ t) → tterm t; (TypeArg T) → ttype T}
      app-ps = recompose-apps asₚ
      fmap = recompose-apps asₜ $ mvar data-fmapₓ
      ftp = recompose-tpapps (as-ttys asₜ) $ mtpvar data-functorₓ
      ptp = recompose-tpapps (as-ttys asₜ) $ mtpvar X in
  foldl (λ {(Ctr _ x Tₓ) rec → rec ≫=maybe λ rec → trie-lookup ms' x ≫=maybe λ t →
    just λ tₕ → mapp (rec tₕ) t}) (just λ t → t) cs ≫=maybe λ msf →
  rename "x" from (add-indices-to-ctxt is Γ) for λ xₓ →
  rename "y" from (add-indices-to-ctxt is Γ) for λ yₓ →
  rename "z" from (add-indices-to-ctxt is Γ) for λ zₓ →
  let μ'ₓ  = "/" ^ Xₒ ^ "/mu'"
      --μ'ₓ' = "/" ^ X ^ "/mu'"
      μTₓ  = "/" ^ Xₒ ^ "/mu-type"
      out = λ tₛ → case (x? , env-lookup Γ μ'ₓ) of uncurry λ {(just x) _ → tₛ , nothing; nothing (just (term-udef _ _ out , zₓ , _)) → mapp (recompose-apps asᵢ out) tₛ , just zₓ; nothing _ → mapp (indices-to-apps is $ mappe (AppTp (mvar fixpoint-outₓ) ftp) fmap) tₛ , nothing}
      body = λ Tₛ tₛ fₛ → msf $
             elim-pair (out tₛ) (λ out Xₛ? →
             AppTp (mapp (indices-to-apps is $ AppTp (app-ps $ mvar data-functor-indₓ) Tₛ) out) $
             indices-to-tplams is $ TpLambda pi-gen pi-gen xₓ (Tkt $ indices-to-tpapps is $ TpApp ftp Tₛ) $ TpAppt (indices-to-tpapps is Tₘ) (mapp (mappe (AppTp (mvar fixpoint-inₓ) ftp) fmap) $ mapp (indices-to-apps is fₛ) $ mvar xₓ))
  in
  maybe-else' x?
    -- μ'
     (just $
     elim-pair (out t) λ out Xₛ? →
     let Tₛ = maybe-else' Xₛ? ptp (λ _ → mtpvar Xₒ)
         fₛ = maybe-else' Xₛ? (indices-to-lams is $ Lam pi-gen NotErased pi-gen xₓ (SomeClass $ Tkt $ TpApp ftp ptp) $ mvar xₓ) mvar in
     (msf $ AppTp (mapp (indices-to-apps is $ AppTp (app-ps $ mvar data-functor-indₓ) Tₛ) out) $
             indices-to-tplams is $ TpLambda pi-gen pi-gen xₓ (Tkt $ indices-to-tpapps is $ TpApp ftp Tₛ) $ TpAppt (indices-to-tpapps is Tₘ) (mapp (mappe (AppTp (mvar fixpoint-inₓ) ftp) fmap) $ mapp (indices-to-apps is fₛ) $ mvar xₓ)) , Γ)
    
    -- μ x
    λ ihₓ →
      rename (ihₓ ^ "-mu'") from (add-indices-to-ctxt is Γ) for λ ih-mu'ₓ →
      let Rₓ = mu-name-type ihₓ --ihₓ ^ "/" ^ X
          rvlₓ = mu-name-cast ihₓ in
      just $
        (mapp (flip AppTp Tₘ $ flip mapp t $ recompose-apps asᵢ $ mappe (AppTp (mvar fixpoint-indₓ) ftp) fmap) $
         Mlam Rₓ $ Mlam rvlₓ $ Mlam ih-mu'ₓ $ mlam ihₓ $ indices-to-lams is $ mlam xₓ $
         Let pi-gen (DefTerm pi-gen zₓ NoType $ mappe (AppTp (AppTp (mvar $ castₓ) $ TpApp ftp $ mtpvar Rₓ) $ TpApp ftp ptp) $ mappe (AppTp (AppTp fmap $ mtpvar Rₓ) ptp) $ mvar rvlₓ) $
         Let pi-gen (DefTerm pi-gen rvlₓ NoType $
           mappe (AppTp (AppTp (mvar castₓ) $ mtpvar Rₓ) ptp) $ mvar rvlₓ) $
         body (mtpvar Rₓ) (mvar xₓ) (mvar zₓ)) ,
        ctxt-μ-out-def ("/" ^ rename-validify Rₓ ^ "/mu'") (Phi pi-gen (IotaProj (mvar ih-mu'ₓ) "2" pi-gen) (IotaProj (mvar ih-mu'ₓ) "1" pi-gen) (mvar fixpoint-outₓ) pi-gen) zₓ (ctxt-rename ("/" ^ rename-validify Rₓ) ("/" ^ X) Γ)

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
    elab-mu = mendler-elab-mu;
    elab-mu-pure = mendler-elab-mu-pure
  }

selected-encoding = case cedille-options.options.datatype-encoding options of λ where
  cedille-options.Mendler → mendler-simple-encoding
  cedille-options.Mendler-old → mendler-encoding
