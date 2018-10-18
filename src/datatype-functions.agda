module datatype-functions where
open import lib
open import ctxt
open import syntax-util
open import general-util
open import cedille-types
open import subst
open import rename
open import is-free

data indx : Set where
  Index : var → tk → indx

data ctr : Set where
  Ctr : var → type → ctr

parameters = 𝕃 decl
indices = 𝕃 indx
constructors = 𝕃 ctr

data datatype : Set where
  Data : var → parameters → indices → constructors → datatype

params-to-parameters : params → parameters
params-to-parameters ParamsNil = []
params-to-parameters (ParamsCons p ps) = p :: params-to-parameters ps

{-# TERMINATING #-}
decompose-arrows : ctxt → type → parameters × type
decompose-arrows Γ (Abs pi me pi' x atk T) =
  let x' = fresh-var x (ctxt-binds-var Γ) empty-renamectxt in
  case decompose-arrows (ctxt-var-decl x' Γ) (rename-var Γ x x' T) of λ where
    (ps , T') → Decl posinfo-gen posinfo-gen me x' atk posinfo-gen :: ps , T'
decompose-arrows Γ (TpArrow T me T') =
  let x = fresh-var "x" (ctxt-binds-var Γ) empty-renamectxt in
  case decompose-arrows (ctxt-var-decl x Γ) T' of λ where
    (ps , T'') → Decl posinfo-gen posinfo-gen me x (Tkt T) posinfo-gen :: ps , T''
decompose-arrows Γ (TpParens pi T pi') = decompose-arrows Γ T
decompose-arrows Γ T = [] , T

decompose-ctr-type : ctxt → type → type × parameters × 𝕃 tty
decompose-ctr-type Γ T with decompose-arrows Γ T
...| ps , Tᵣ with decompose-tpapps Tᵣ
...| Tₕ , as = Tₕ , ps , as

{-# TERMINATING #-}
kind-to-indices : ctxt → kind → indices
kind-to-indices Γ (KndArrow k k') =
  let x' = fresh-var "x" (ctxt-binds-var Γ) empty-renamectxt in
  Index x' (Tkk k) :: kind-to-indices (ctxt-var-decl x' Γ) k'
kind-to-indices Γ (KndParens pi k pi') = kind-to-indices Γ k
kind-to-indices Γ (KndPi pi pi' x atk k) =
  let x' = fresh-var x (ctxt-binds-var Γ) empty-renamectxt in
  Index x' atk :: kind-to-indices (ctxt-var-decl x' Γ) k
kind-to-indices Γ (KndTpArrow T k) =
  let x' = fresh-var "x" (ctxt-binds-var Γ) empty-renamectxt in
  Index x' (Tkt T) :: kind-to-indices (ctxt-var-decl x' Γ) k
kind-to-indices Γ (KndVar pi x as) with ctxt-lookup-kind-var-def Γ x
...| nothing = []
...| just (ps , k) = kind-to-indices Γ $ fst $ subst-params-args Γ ps as k
kind-to-indices Γ (Star pi) = []

dataConsts-to-ctrs : dataConsts → constructors
dataConsts-to-ctrs DataNull = []
dataConsts-to-ctrs (DataCons (DataConst _ x T) cs) = Ctr x T :: dataConsts-to-ctrs cs

defDatatype-to-datatype : ctxt → defDatatype → datatype
defDatatype-to-datatype Γ (Datatype _ _ x ps k dcs _) =
  Data x (params-to-parameters ps) (kind-to-indices Γ k) (dataConsts-to-ctrs dcs)

tk-erased : tk → maybeErased → maybeErased
tk-erased (Tkk _) me = Erased
tk-erased (Tkt _) me = me

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
  (Decl pi pi' me x atk pi'') → Abs pi (tk-erased atk me) pi' x atk

indices-to-lams : indices → (body : term) → term
indices-to-lams = flip $ foldr λ where
  (Index x atk) → Lam posinfo-gen Erased posinfo-gen x (SomeClass atk)

indices-to-lams' : indices → (body : term) → term
indices-to-lams' = flip $ foldr λ where
  (Index x atk) → Lam posinfo-gen Erased posinfo-gen x NoClass

parameters-to-lams : parameters → (body : term) → term
parameters-to-lams = flip $ foldr λ where
  (Decl pi pi' me x atk pi'') → Lam pi (tk-erased atk me) pi' x (SomeClass atk)

parameters-to-lams' : parameters → (body : term) → term
parameters-to-lams' = flip $ foldr λ where
  (Decl pi pi' me x atk pi'') → Lam pi (tk-erased atk me) pi' x NoClass

indices-to-apps : indices → (body : term) → term
indices-to-apps = flip $ foldl λ where
  (Index x (Tkt T)) t → App t Erased (mvar x)
  (Index x (Tkk k)) t → AppTp t (mtpvar x)

parameters-to-apps : parameters → (body : term) → term
parameters-to-apps = flip $ foldl λ where
  (Decl pi pi' me x (Tkt T) pi'') t → App t me (mvar x)
  (Decl pi pi' me x (Tkk k) pi'') t → AppTp t (mtpvar x)

indices-to-tpapps : indices → (body : type) → type
indices-to-tpapps = flip $ foldl λ where
  (Index x (Tkt T)) T' → TpAppt T' (mvar x)
  (Index x (Tkk k)) T  → TpApp  T  (mtpvar x)

parameters-to-tpapps : parameters → (body : type) → type
parameters-to-tpapps = flip $ foldl λ where
  (Decl pi pi' me x (Tkt T) pi'') T' → TpAppt T' (mvar x)
  (Decl pi pi' me x (Tkk k) pi'') T  → TpApp  T  (mtpvar x)

constructors-to-lams' : constructors → (body : term) → term
constructors-to-lams' = flip $ foldr λ where
  (Ctr x T) → Lam posinfo-gen NotErased posinfo-gen x NoClass

constructors-to-lams : ctxt → var → parameters → constructors → (body : term) → term
constructors-to-lams Γ x ps cs t = foldr
  (λ {(Ctr y T) f Γ → Lam posinfo-gen NotErased posinfo-gen y
    (SomeClass $ Tkt $ subst Γ (parameters-to-tpapps ps $ mtpvar y) y T)
    $ f $ ctxt-var-decl y Γ})
  (λ Γ → t) cs Γ

add-indices-to-ctxt : indices → ctxt → ctxt
add-indices-to-ctxt = flip $ foldr λ {(Index x atk) → ctxt-var-decl x}

add-parameters-to-ctxt : parameters → ctxt → ctxt
add-parameters-to-ctxt = flip $ foldr λ {(Decl _ _ _ x'' _ _) → ctxt-var-decl x''}

add-constructors-to-ctxt : constructors → ctxt → ctxt
add-constructors-to-ctxt = flip $ foldr λ {(Ctr x T) → ctxt-var-decl x}

open import conversion

{-# TERMINATING #-}
ctr-positive : ctxt → var → type → 𝔹
ctr-positive Γ x T = arrs+ Γ (hnf' Γ T) where

  not-free : ∀ {ed} → ⟦ ed ⟧ → 𝔹
  hnf' : ctxt → type → type
  hnf' Γ T = hnf Γ unfold-all T tt
  type+ : ctxt → type → 𝔹
  kind+ : ctxt → kind → 𝔹
  tk+ : ctxt → tk → 𝔹
  arrs+ : ctxt → type → 𝔹

  arrs+ Γ (Abs _ _ _ x' atk T) =
    let Γ' = ctxt-var-decl x' Γ in
    tk+ Γ atk && arrs+ Γ' (hnf' Γ' T)
  arrs+ Γ (TpApp T T') = arrs+ Γ T && not-free T'
  arrs+ Γ (TpAppt T t) = arrs+ Γ T && not-free t
  arrs+ Γ (TpArrow T _ T') = type+ Γ (hnf' Γ T) && arrs+ Γ (hnf' Γ T')
  arrs+ Γ (TpLambda _ _ x' atk T) =
    let Γ' = ctxt-var-decl x' Γ in
    tk+ Γ atk && arrs+ Γ' (hnf' Γ' T)
  arrs+ Γ (TpVar _ x') = x =string x'
  arrs+ Γ T = ff
  
  type+ Γ (Abs _ _ _ x' atk T) =
    let Γ' = ctxt-var-decl x' Γ in
    type+ Γ' (hnf' Γ' T)
  type+ Γ (Iota _ _ x' T T') = not-free (Iota posinfo-gen posinfo-gen x' T T')
    {-let Γ' = ctxt-var-decl x' Γ in
    type+ Γ (hnf' Γ T) && type+ Γ' (hnf' Γ' T')-}
  type+ Γ (Lft _ _ x' t lT) = not-free $ mlam x' t
  type+ Γ (NoSpans T _) = type+ Γ T
  type+ Γ (TpLet _ (DefTerm _ x' T? t) T) = type+ Γ (hnf' Γ (subst Γ t x' T))
  type+ Γ (TpLet _ (DefType _ x' k T) T') = type+ Γ (hnf' Γ (subst Γ T x' T'))
  type+ Γ (TpApp T T') = type+ Γ T && not-free T'
  type+ Γ (TpAppt T t) = type+ Γ T && not-free t
  type+ Γ (TpArrow T _ T') = type+ Γ (hnf' Γ T') && ~ type+ Γ (hnf' Γ T)
  type+ Γ (TpEq _ tₗ tᵣ _) = tt
  type+ Γ (TpHole _) = tt
  type+ Γ (TpLambda _ _ x' atk T)=
    let Γ' = ctxt-var-decl x' Γ in
    type+ Γ' (hnf' Γ' T)
  type+ Γ (TpParens _ T _) = type+ Γ T
  type+ Γ (TpVar _ x') = tt
  
  kind+ Γ (KndArrow k k') = kind+ Γ k' && ~ kind+ Γ k
  kind+ Γ (KndParens _ k _) = kind+ Γ k
  kind+ Γ (KndPi _ _ x' atk k) = kind+ (ctxt-var-decl x' Γ) k && ~ tk+ Γ atk
  kind+ Γ (KndTpArrow T k) = kind+ Γ k && ~ type+ Γ T
  kind+ Γ (KndVar _ κ as) =
    maybe-else tt (uncurry λ ps k → kind+ Γ (fst (subst-params-args Γ ps as k)))
      (ctxt-lookup-kind-var-def Γ κ)
  kind+ Γ (Star _) = tt

  tk+ Γ (Tkt T) = type+ Γ (hnf' Γ T)
  tk+ Γ (Tkk k) = kind+ Γ k

  not-free = ~_ ∘ is-free-in check-erased x
