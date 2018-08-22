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
add-parameters-to-ctxt = flip $ foldr (λ {(Decl _ _ _ x'' _ _) → ctxt-var-decl' x''})

rename-indices : ctxt → indices → indices
rename-indices Γ is = foldr {B = renamectxt → indices}
  (λ {(Index x atk) is ρ →
     let x' = fresh-var x (ctxt-binds-var Γ) ρ in
     Index x' (substh-tk {TERM} Γ ρ empty-trie atk) :: is (renamectxt-insert ρ x x')})
  (λ ρ → []) is empty-renamectxt


reindex : ∀ {ed} → ctxt → indices → ⟦ ed ⟧ → ⟦ ed ⟧
reindex-term : ctxt → indices → term → term
reindex-type : ctxt → indices → type → type
reindex-kind : ctxt → indices → kind → kind
reindex-tk : ctxt → indices → tk → tk
reindex-liftingType : ctxt → indices → liftingType → liftingType
reindex-optTerm : ctxt → indices → optTerm → optTerm
reindex-optType : ctxt → indices → optType → optType
reindex-optGuide : ctxt → indices → optGuide → optGuide
reindex-optClass : ctxt → indices → optClass → optClass
reindex-lterms : ctxt → indices → lterms → lterms
reindex-args : ctxt → indices → args → args
reindex-arg : ctxt → indices → arg → arg
reindex-defTermOrType : ctxt → indices → defTermOrType → defTermOrType × ctxt

reindex{TERM} = reindex-term
reindex{TYPE} = reindex-type
reindex{KIND} = reindex-kind
reindex{TK}   = reindex-tk
reindex       = λ Γ is x → x

pattern reindex-term-var = "indices"
pattern reindex-type-var = "Indices"

-- Reindexing cases
reindex-term Γ is (App t me (Var pi reindex-term-var)) =
  indices-to-apps is $ reindex-term Γ is t
reindex-term Γ is (Lam pi me pi' reindex-term-var (SomeClass (Tkt (TpVar pi'' reindex-type-var))) t) =
  indices-to-lams is $ reindex-term Γ is t
reindex-term Γ is (Lam pi me pi' reindex-term-var NoClass t) =
  indices-to-lams' is $ reindex-term Γ is t
-- Other cases
reindex-term Γ is (App t me t') =
  App (reindex-term Γ is t) me (reindex-term Γ is t')
reindex-term Γ is (AppTp t T) =
  AppTp (reindex-term Γ is t) (reindex-type Γ is T)
reindex-term Γ is (Beta pi ot ot') =
  Beta pi (reindex-optTerm Γ is ot) (reindex-optTerm Γ is ot')
reindex-term Γ is (Chi pi oT t) =
  Chi pi (reindex-optType Γ is oT) (reindex-term Γ is t)
reindex-term Γ is (Delta pi oT t) =
  Delta pi (reindex-optType Γ is oT) (reindex-term Γ is t)
reindex-term Γ is (Epsilon pi lr m t) =
  Epsilon pi lr m (reindex-term Γ is t)
reindex-term Γ is (Hole pi) =
  Hole pi
reindex-term Γ is (IotaPair pi t t' g pi') =
  IotaPair pi (reindex-term Γ is t) (reindex-term Γ is t') (reindex-optGuide Γ is g) pi'
reindex-term Γ is (IotaProj t n pi) =
  IotaProj (reindex-term Γ is t) n pi
reindex-term Γ is (Lam pi me pi' x oc t) =
  Lam pi me pi' x (reindex-optClass Γ is oc) (reindex-term (ctxt-var-decl' x Γ) is t)
reindex-term Γ is (Let pi d t) =
  flip uncurry (reindex-defTermOrType Γ is d) λ d' Γ' → Let pi d' (reindex-term Γ' is t)
reindex-term Γ is (Open pi x t) =
  Open pi x (reindex-term Γ is t)
reindex-term Γ is (Parens pi t pi') =
  reindex-term Γ is t
reindex-term Γ is (Phi pi t₌ t₁ t₂ pi') =
  Phi pi (reindex-term Γ is t₌) (reindex-term Γ is t₁) (reindex-term Γ is t₂) pi'
reindex-term Γ is (Rho pi op on t og t') =
  Rho pi op on (reindex-term Γ is t) (reindex-optGuide Γ is og) (reindex-term Γ is t')
reindex-term Γ is (Sigma pi t) =
  Sigma pi (reindex-term Γ is t)
reindex-term Γ is (Theta pi θ t ts) =
  Theta pi θ (reindex-term Γ is t) (reindex-lterms Γ is ts)
reindex-term Γ is (Var pi x) =
  Var pi x

-- Reindexing cases
reindex-type Γ is (TpAppt T (Var pi reindex-term-var)) =
  indices-to-tpapps is $ reindex-type Γ is T
reindex-type Γ is (TpLambda pi pi' reindex-term-var (Tkt (TpVar pi'' reindex-type-var)) T) =
  indices-to-tplams is $ reindex-type Γ is T
reindex-type Γ is (Abs pi me pi' reindex-term-var (Tkt (TpVar pi'' reindex-type-var)) T) =
  indices-to-alls is $ reindex-type Γ is T
-- Other cases
reindex-type Γ is (Abs pi me pi' x atk T) =
  Abs pi me pi' x (reindex-tk Γ is atk) (reindex-type (ctxt-var-decl' x Γ) is T)
reindex-type Γ is (Iota pi pi' x T T') =
  Iota pi pi' x (reindex-type Γ is T) (reindex-type (ctxt-var-decl' x Γ) is T')
reindex-type Γ is (Lft pi pi' x t lT) =
  Lft pi pi' x (reindex-term (ctxt-var-decl' x Γ) is t) (reindex-liftingType Γ is lT)
reindex-type Γ is (NoSpans T pi) =
  NoSpans (reindex-type Γ is T) pi
reindex-type Γ is (TpLet pi d T) =
  flip uncurry (reindex-defTermOrType Γ is d) λ d' Γ' → TpLet pi d' (reindex-type Γ' is T)
reindex-type Γ is (TpApp T T') =
  TpApp (reindex-type Γ is T) (reindex-type Γ is T')
reindex-type Γ is (TpAppt T t) =
  TpAppt (reindex-type Γ is T) (reindex-term Γ is t)
reindex-type Γ is (TpArrow T me T') =
  TpArrow (reindex-type Γ is T) me (reindex-type Γ is T')
reindex-type Γ is (TpEq pi t t' pi') =
  TpEq pi (reindex-term Γ is t) (reindex-term Γ is t') pi'
reindex-type Γ is (TpHole pi) =
  TpHole pi
reindex-type Γ is (TpLambda pi pi' x atk T) =
  TpLambda pi pi' x (reindex-tk Γ is atk) (reindex-type (ctxt-var-decl' x Γ) is T)
reindex-type Γ is (TpParens pi T pi') =
  reindex-type Γ is T
reindex-type Γ is (TpVar pi x) =
  TpVar pi x

-- Reindexing cases
reindex-kind Γ is (KndTpArrow (TpVar pi reindex-type-var) k) =
  indices-to-kind is $ reindex-kind Γ is k
reindex-kind Γ is (KndPi pi pi' reindex-term-var (Tkt (TpVar pi'' reindex-type-var)) k) =
  indices-to-kind is $ reindex-kind Γ is k
-- Other cases
reindex-kind Γ is (KndParens pi k pi') =
  reindex-kind Γ is k
reindex-kind Γ is (KndArrow k k') =
  KndArrow (reindex-kind Γ is k) (reindex-kind Γ is k')
reindex-kind Γ is (KndPi pi pi' x atk k) =
  KndPi pi pi' x (reindex-tk Γ is atk) (reindex-kind (ctxt-var-decl' x Γ) is k)
reindex-kind Γ is (KndTpArrow T k) =
  KndTpArrow (reindex-type Γ is T) (reindex-kind Γ is k)
reindex-kind Γ is (KndVar pi x as) =
  KndVar pi x (reindex-args Γ is as)
reindex-kind Γ is (Star pi) =
  Star pi

reindex-tk Γ is (Tkt T) = Tkt $ reindex-type Γ is T
reindex-tk Γ is (Tkk k) = Tkk $ reindex-kind Γ is k

-- Can't reindex large indices in a lifting type (LiftPi requires a type, not a tk),
-- so for now we will just ignore reindexing lifting types.
-- Types withing lifting types will still be reindexed, though.
reindex-liftingType Γ is (LiftArrow lT lT') =
  LiftArrow (reindex-liftingType Γ is lT) (reindex-liftingType Γ is lT')
reindex-liftingType Γ is (LiftParens pi lT pi') =
  reindex-liftingType Γ is lT
reindex-liftingType Γ is (LiftPi pi x T lT) =
  LiftPi pi x (reindex-type Γ is T) (reindex-liftingType (ctxt-var-decl' x Γ) is lT)
reindex-liftingType Γ is (LiftStar pi) =
  LiftStar pi
reindex-liftingType Γ is (LiftTpArrow T lT) =
  LiftTpArrow (reindex-type Γ is T) (reindex-liftingType Γ is lT)

reindex-optTerm Γ is NoTerm = NoTerm
reindex-optTerm Γ is (SomeTerm t pi) = SomeTerm (reindex-term Γ is t) pi

reindex-optType Γ is NoType = NoType
reindex-optType Γ is (SomeType T) = SomeType (reindex-type Γ is T)

reindex-optClass Γ is NoClass = NoClass
reindex-optClass Γ is (SomeClass atk) = SomeClass (reindex-tk Γ is atk)

reindex-optGuide Γ is NoGuide = NoGuide
reindex-optGuide Γ is (Guide pi x T) = Guide pi x (reindex-type Γ is T)

reindex-lterms Γ is (LtermsNil pi) = LtermsNil pi
reindex-lterms Γ is (LtermsCons me t ts) =
  LtermsCons me (reindex-term Γ is t) (reindex-lterms Γ is ts)

reindex-arg Γ is (TermArg me t) = TermArg me (reindex-term Γ is t)
reindex-arg Γ is (TypeArg T) = TypeArg (reindex-type Γ is T)

reindex-args Γ is ArgsNil = ArgsNil
reindex-args Γ is (ArgsCons a as) = ArgsCons (reindex-arg Γ is a) (reindex-args Γ is as)

reindex-defTermOrType Γ is (DefTerm pi x oT t) =
  DefTerm pi x (reindex-optType Γ is oT) (reindex-term Γ is t) , ctxt-var-decl' x Γ
reindex-defTermOrType Γ is (DefType pi x k T) =
  DefType pi x (reindex-kind Γ is k) (reindex-type Γ is T) , ctxt-var-decl' x Γ

reindex-dtt-name : ctxt → renamectxt → defTermOrType → defTermOrType × renamectxt
reindex-dtt-name Γ ρ (DefTerm pi x oT t) =
  rename x - x from ρ for λ x' → _,_ $
    DefTerm pi x' (optType-map oT $ subst-renamectxt Γ ρ) (subst-renamectxt Γ ρ t)
reindex-dtt-name Γ ρ (DefType pi x k T) =
  rename x - x from ρ for λ x' → _,_ $
    DefType pi x' (subst-renamectxt Γ ρ k) (subst-renamectxt Γ ρ T)

reindex-cmds : ctxt → indices → renamectxt → cmds → cmds × renamectxt
reindex-cmds Γ is ρ CmdsStart = CmdsStart , ρ
reindex-cmds Γ is ρ (CmdsNext (ImportCmd i) cs) =
  flip uncurry (reindex-cmds Γ is ρ cs) $ _,_ ∘ CmdsNext (ImportCmd i)
reindex-cmds Γ is ρ (CmdsNext (DefTermOrType op d pi) cs) =
  flip uncurry (reindex-dtt-name Γ ρ d) λ d' ρ' →
  flip uncurry (reindex-defTermOrType Γ is d') λ d'' Γ' →
  flip uncurry (reindex-cmds Γ' is ρ' cs) $ _,_ ∘ CmdsNext (DefTermOrType op d'' pi)
reindex-cmds Γ is ρ (CmdsNext (DefKind pi x ps k pi') cs) =
  rename x - x from ρ for λ x' ρ' →
  flip uncurry (reindex-cmds (ctxt-var-decl' x' Γ) is ρ' cs) $ _,_ ∘ CmdsNext
    (DefKind pi x' ps (reindex-kind (add-parameters-to-ctxt (params-to-parameters ps) Γ) is $
       subst-renamectxt Γ ρ k) pi')

reindex-file : ctxt → indices → start → cmds × renamectxt
reindex-file Γ is (File pi csᵢ pi' pi'' x
      (ParamsCons (Decl _ _ _ reindex-type-var (Tkk (Star _)) _) ps) cs pi''') =
  reindex-cmds Γ is empty-renamectxt cs
reindex-file Γ is (File pi csᵢ pi' pi'' x ps cs pi''') =
  reindex-cmds Γ is empty-renamectxt cs


