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
open import toplevel-state options {id}
open import spans options {id}


ctxt-var-decl' = ctxt-var-decl posinfo-gen

uncurry' : ∀ {A B C D : Set} → (A → B → C → D) → (A × B × C) → D
uncurry' f (a , b , c) = f a b c

uncurry'' : ∀ {A B C D E : Set} → (A → B → C → D → E) → (A × B × C × D) → E
uncurry'' f (a , b , c , d) = f a b c d

ctxt-term-decl' : posinfo → var → type → ctxt → ctxt
ctxt-term-decl' pi x T (mk-ctxt (fn , mn , ps , q) ss is os) =
  mk-ctxt (fn , mn , ps , trie-insert q x (x , ArgsNil)) ss
    (trie-insert is x (term-decl T , fn , pi)) os

ctxt-type-decl' : posinfo → var → kind → ctxt → ctxt
ctxt-type-decl' pi x k (mk-ctxt (fn , mn , ps , q) ss is os) =
  mk-ctxt (fn , mn , ps , trie-insert q x (x , ArgsNil)) ss
    (trie-insert is x (type-decl k , fn , pi)) os

ctxt-tk-decl' : posinfo → var → tk → ctxt → ctxt
ctxt-tk-decl' pi x (Tkt T) = ctxt-term-decl' pi x T
ctxt-tk-decl' pi x (Tkk k) = ctxt-type-decl' pi x k

ctxt-param-decl : var → var → tk → ctxt → ctxt
ctxt-param-decl x x' atk Γ @ (mk-ctxt (fn , mn , ps , q) ss is os) =
  let d = case atk of λ {(Tkt T) → term-decl T; (Tkk k) → type-decl k} in
  mk-ctxt
  (fn , mn , ps , trie-insert q x (mn # x , ArgsNil)) ss
  (trie-insert is x' (d , fn , posinfo-gen)) os

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
  mk-ctxt (fn , mn , ps , trie-insert q x (x , ArgsNil)) ss
    (trie-insert is x (term-def nothing OpacTrans t T , fn , pi)) os

ctxt-let-type-def : posinfo → var → type → kind → ctxt → ctxt
ctxt-let-type-def pi x T k (mk-ctxt (fn , mn , ps , q) ss is os) =
  mk-ctxt (fn , mn , ps , trie-insert q x (x , ArgsNil)) ss
    (trie-insert is x (type-def nothing OpacTrans T k , fn , pi)) os

ctxt-kind-def' : var → var → params → kind → ctxt → ctxt
ctxt-kind-def' x x' ps2 k Γ @ (mk-ctxt (fn , mn , ps1 , q) ss is os) = mk-ctxt
  (fn , mn , ps1 , qualif-insert-params q (mn # x) x ps1) ss
  (trie-insert is x' (kind-def ps1 (h Γ ps2) k' , fn , posinfo-gen)) os
  where
    k' = hnf Γ unfold-head k tt
    h : ctxt → params → params
    h Γ (ParamsCons (Decl pi pi' me x atk pi'') ps) =
      ParamsCons (Decl pi pi' me (pi' % x) (qualif-tk Γ atk) pi'') (h (ctxt-tk-decl pi' localScope x atk Γ) ps)
    h _ ps = ps

ctxt-lookup-term-var' : ctxt → var → maybe type
ctxt-lookup-term-var' Γ @ (mk-ctxt (fn , mn , ps , q) ss is os) x =
  env-lookup Γ x ≫=maybe λ where
    (term-decl T , _) → just T
    (term-def ps _ _ T , _ , x') →
      let ps = maybe-else ParamsNil id ps in
      just $ abs-expand-type ps T
    _ → nothing

-- TODO: Could there be parameter/argument clashes if the same parameter variable is defined multiple times?
-- TODO: Could variables be parameter-expanded multiple times?
ctxt-lookup-type-var' : ctxt → var → maybe kind
ctxt-lookup-type-var' Γ @ (mk-ctxt (fn , mn , ps , q) ss is os) x =
  env-lookup Γ x ≫=maybe λ where
    (type-decl k , _) → just k
    (type-def ps _ _ k , _ , x') →
      let ps = maybe-else ParamsNil id ps in
      just $ abs-expand-kind ps k
    _ → nothing

subst : ∀ {ed ed' : exprd} → ctxt → ⟦ ed' ⟧ → var → ⟦ ed ⟧ → ⟦ ed ⟧
subst{TERM} = subst-term
subst{TYPE} = subst-type
subst{KIND} = subst-kind
subst Γ _ _ x = x

subst-renamectxt : ∀ {ed : exprd} → ctxt → renamectxt → ⟦ ed ⟧ → ⟦ ed ⟧
subst-renamectxt{TERM} Γ ρ = substh-term {LIFTINGTYPE} Γ ρ empty-trie
subst-renamectxt{TYPE} Γ ρ = substh-type {LIFTINGTYPE} Γ ρ empty-trie
subst-renamectxt{KIND} Γ ρ = substh-kind {LIFTINGTYPE} Γ ρ empty-trie
subst-renamectxt        Γ ρ = id

renamectxt-single : var → var → renamectxt
renamectxt-single = renamectxt-insert empty-renamectxt

rename-var : ∀ {ed : exprd} → ctxt → var → var → ⟦ ed ⟧ → ⟦ ed ⟧
rename-var Γ x x' = subst-renamectxt Γ (renamectxt-single x x')
-- rename-var {TERM} Γ x x' = substh-term {LIFTINGTYPE} Γ (renamectxt-single x x') empty-trie
-- rename-var {TYPE} Γ x x' = substh-type {LIFTINGTYPE} Γ (renamectxt-single x x') empty-trie
-- rename-var {KIND} Γ x x' = substh-kind {LIFTINGTYPE} Γ (renamectxt-single x x') empty-trie
-- rename-var Γ x x' = id

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
mbeta t t' = Beta posinfo-gen (SomeTerm t posinfo-gen) (SomeTerm t' posinfo-gen)
mrho t x T t' = Rho posinfo-gen RhoPlain NoNums t (Guide posinfo-gen x T) t'
mtpeq t1 t2 = TpEq posinfo-gen t1 t2 posinfo-gen

subst-args-params : ctxt → args → params → kind → kind
subst-args-params Γ (ArgsCons (TermArg _ t) ys) (ParamsCons (Decl _ _ _ x _ _) ps) k =
  subst-args-params Γ ys ps $ subst-kind Γ t x k
subst-args-params Γ (ArgsCons (TypeArg t) ys) (ParamsCons (Decl _ _ _ x _ _) ps) k =
  subst-args-params Γ ys ps $ subst-kind Γ t x k
subst-args-params Γ ys ps k = k

data indx : Set where
  Index : var → tk → indx
parameters = 𝕃 decl
indices = 𝕃 indx

indices-to-kind : indices → kind → kind
indices-to-kind = flip $ foldr λ {(Index x atk) → KndPi posinfo-gen posinfo-gen x atk}

parameters-to-kind : parameters → kind → kind
parameters-to-kind = flip $ foldr λ {(Decl pi pi' me x atk pi'') → KndPi pi pi' x atk}

indices-to-tplams : indices → (body : type) → type
indices-to-tplams = flip $ foldr λ where
  (Index x atk) → TpLambda posinfo-gen posinfo-gen x atk

parameters-to-tplams : parameters → (body : type) → type
parameters-to-tplams = flip $ foldr λ where
  (Decl pi pi' me x atk pi'') → TpLambda pi pi' x atk

indices-to-alls : indices → (body : type) → type
indices-to-alls = flip $ foldr λ where
  (Index x atk) → Abs posinfo-gen Erased posinfo-gen x atk

parameters-to-alls : parameters → (body : type) → type
parameters-to-alls = flip $ foldr λ where
  (Decl pi pi' me x atk pi'') → Abs pi me pi' x atk

indices-to-lams : indices → (body : term) → term
indices-to-lams = flip $ foldr λ where
  (Index x atk) → Lam posinfo-gen Erased posinfo-gen x (SomeClass atk)

indices-to-lams' : indices → (body : term) → term
indices-to-lams' = flip $ foldr λ where
  (Index x atk) → Lam posinfo-gen Erased posinfo-gen x NoClass

parameters-to-lams : parameters → (body : term) → term
parameters-to-lams = flip $ foldr λ where
  (Decl pi pi' me x atk pi'') → Lam pi Erased pi' x (SomeClass atk)

parameters-to-lams' : parameters → (body : term) → term
parameters-to-lams' = flip $ foldr λ where
  (Decl pi pi' me x atk pi'') → Lam pi Erased pi' x NoClass

indices-to-apps : indices → (body : term) → term
indices-to-apps = flip $ foldl λ where
  (Index x (Tkt T)) t → App t Erased (mvar x)
  (Index x (Tkk k)) t → AppTp t (mtpvar x)

parameters-to-apps : parameters → (body : term) → term
parameters-to-apps = flip $ foldl λ where
  (Decl pi pi' me x (Tkt T) pi'') t → App t Erased (mvar x)
  (Decl pi pi' me x (Tkk k) pi'') t → AppTp t (mtpvar x)

indices-to-tpapps : indices → (body : type) → type
indices-to-tpapps = flip $ foldl λ where
  (Index x (Tkt T)) T' → TpAppt T' (mvar x)
  (Index x (Tkk k)) T  → TpApp  T  (mtpvar x)

parameters-to-tpapps : parameters → (body : type) → type
parameters-to-tpapps = flip $ foldl λ where
  (Decl pi pi' me x (Tkt T) pi'') T' → TpAppt T' (mvar x)
  (Decl pi pi' me x (Tkk k) pi'') T  → TpApp  T  (mtpvar x)


params-to-parameters : params → parameters
params-to-parameters ParamsNil = []
params-to-parameters (ParamsCons p ps) = p :: params-to-parameters ps

add-indices-to-ctxt : indices → ctxt → ctxt
add-indices-to-ctxt = flip $ foldr λ {(Index x atk) → ctxt-var-decl' x}

add-parameters-to-ctxt : parameters → ctxt → ctxt
add-parameters-to-ctxt = flip $ foldr λ {(Decl _ _ _ x'' _ _) → ctxt-var-decl' x''}

module reindexing (Γ : ctxt) (isₒ : indices) where

  reindex-fresh-var : renamectxt → trie indices → var → var
  reindex-fresh-var ρ is "_" = "_"
  reindex-fresh-var ρ is x = fresh-var x (λ x' → ctxt-binds-var Γ x' || trie-contains is x') ρ

  rename-indices : trie indices → indices
  rename-indices is = foldr {B = renamectxt → indices}
    (λ {(Index x atk) f ρ →
       let x' = reindex-fresh-var ρ is x in
       Index x' (substh-tk {TERM} Γ ρ empty-trie atk) :: f (renamectxt-insert ρ x x')})
    (λ ρ → []) isₒ empty-renamectxt
  
  reindex-t : Set → Set
  reindex-t X = renamectxt → trie indices → X → X
  
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
  ...| tt with rename-indices is | oc
  ...| isₙ | NoClass = indices-to-lams' isₙ $ reindex-term (rc-is ρ isₙ) (trie-insert is x isₙ) t
  ...| isₙ | SomeClass atk = indices-to-lams isₙ $ reindex-term (rc-is ρ isₙ) (trie-insert is x isₙ) t
  reindex-term ρ is (Let pi d t) =
    flip uncurry (reindex-defTermOrType ρ is d) λ d' ρ' → Let pi d' (reindex-term ρ' is t)
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

  reindex-type ρ is (Abs pi me pi' x atk T) with is-index-var x
  ...| ff = let x' = reindex-fresh-var ρ is x in
    Abs pi me pi' x' (reindex-tk ρ is atk) (reindex-type (renamectxt-insert ρ x x') is T)
  ...| tt = let isₙ = rename-indices is in
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
    flip uncurry (reindex-defTermOrType ρ is d) λ d' ρ' → TpLet pi d' (reindex-type ρ' is T)
  reindex-type ρ is (TpApp T T') =
    TpApp (reindex-type ρ is T) (reindex-type ρ is T')
  reindex-type ρ is (TpAppt T (Var pi x)) with trie-lookup is x
  ...| nothing = TpAppt (reindex-type ρ is T) (reindex-term ρ is (Var pi x))
  ...| just is' = indices-to-tpapps is' $ reindex-type ρ is T
  reindex-type ρ is (TpAppt T t) =
    TpAppt (reindex-type ρ is T) (reindex-term ρ is t)
  reindex-type ρ is (TpArrow T me T') =
    TpArrow (reindex-type ρ is T) me (reindex-type ρ is T')
  reindex-type ρ is (TpEq pi t t' pi') =
    TpEq pi (reindex-term ρ is t) (reindex-term ρ is t') pi'
  reindex-type ρ is (TpHole pi) =
    TpHole pi
  reindex-type ρ is (TpLambda pi pi' x atk T) with is-index-var x
  ...| ff = let x' = reindex-fresh-var ρ is x in
    TpLambda pi pi' x' (reindex-tk ρ is atk) (reindex-type (renamectxt-insert ρ x x') is T)
  ...| tt = let isₙ = rename-indices is in
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
  ...| tt = let isₙ = rename-indices is in
    indices-to-kind isₙ $ reindex-kind (rc-is ρ isₙ) (trie-insert is x isₙ) k
  reindex-kind ρ is (KndTpArrow (TpVar pi x) k) with is-index-type-var x
  ...| ff = KndTpArrow (reindex-type ρ is (TpVar pi x)) (reindex-kind ρ is k)
  ...| tt = let isₙ = rename-indices is in
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
  
  reindex-lterms ρ is (LtermsNil pi) = LtermsNil pi
  reindex-lterms ρ is (LtermsCons me t ts) =
    LtermsCons me (reindex-term ρ is t) (reindex-lterms ρ is ts)

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
  
  reindex-args ρ is ArgsNil = ArgsNil
  reindex-args ρ is (ArgsCons a as) = ArgsCons (reindex-arg ρ is a) (reindex-args ρ is as)
  
  reindex-defTermOrType ρ is (DefTerm pi x oT t) =
    let x' = reindex-fresh-var ρ is x in
    DefTerm pi x' (reindex-optType ρ is oT) (reindex-term ρ is t) , renamectxt-insert ρ x x'
  reindex-defTermOrType ρ is (DefType pi x k T) =
    let x' = reindex-fresh-var ρ is x in
    DefType pi x (reindex-kind ρ is k) (reindex-type ρ is T) , renamectxt-insert ρ x x'

  reindex-cmds : renamectxt → trie indices → cmds → cmds × renamectxt
  reindex-cmds ρ is CmdsStart = CmdsStart , ρ
  reindex-cmds ρ is (CmdsNext (ImportCmd i) cs) =
    flip uncurry (reindex-cmds ρ is cs) $ _,_ ∘ CmdsNext (ImportCmd i)
  reindex-cmds ρ is (CmdsNext (DefTermOrType op d pi) cs) =
    flip uncurry (reindex-defTermOrType ρ is d) λ d' ρ' →
    flip uncurry (reindex-cmds ρ' is cs) $ _,_ ∘ CmdsNext (DefTermOrType op d' pi)
  reindex-cmds ρ is (CmdsNext (DefKind pi x ps k pi') cs) =
    let x' = reindex-fresh-var ρ is x in
    flip uncurry (reindex-cmds (renamectxt-insert ρ x x') is cs) $ _,_ ∘ CmdsNext
      (DefKind pi x' ps (reindex-kind ρ is k) pi')
  

reindex-file : ctxt → indices → start → cmds × renamectxt
reindex-file Γ is (File pi csᵢ pi' pi'' x ps cs pi''') =
  reindex-cmds empty-renamectxt empty-trie cs
  where open reindexing Γ is

