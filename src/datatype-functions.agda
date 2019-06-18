module datatype-functions where
open import ctxt
open import syntax-util
open import general-util
open import type-util
open import cedille-types
open import subst
open import rename
open import free-vars

data indx : Set where
  Index : var → tpkd → indx
indices = 𝕃 indx

data datatype : Set where
  Data : var → params → indices → ctrs → datatype

{-# TERMINATING #-}
decompose-arrows : ctxt → type → params × type
decompose-arrows Γ (TpAbs me x atk T) =
  let x' = fresh-var-new Γ x in
  case decompose-arrows (ctxt-var-decl x' Γ) (rename-var Γ x x' T) of λ where
    (ps , T') → Param me x' atk :: ps , T'
decompose-arrows Γ T = [] , T

decompose-ctr-type : ctxt → type → type × params × 𝕃 tmtp
decompose-ctr-type Γ T with decompose-arrows Γ T
...| ps , Tᵣ with decompose-tpapps Tᵣ
...| Tₕ , as = Tₕ , ps , as

{-# TERMINATING #-}
kind-to-indices : ctxt → kind → indices
kind-to-indices Γ (KdAbs x atk k) =
  let x' = fresh-var-new Γ x in
  Index x' atk :: kind-to-indices (ctxt-var-decl x' Γ) (rename-var Γ x x' k)
kind-to-indices Γ _ = []

rename-indices-h : ctxt → renamectxt → indices → 𝕃 tmtp → indices
rename-indices-h Γ ρ (Index x atk :: is) (ty :: tys) =
  Index x' atk' ::
    rename-indices-h (ctxt-var-decl x' Γ) (renamectxt-insert ρ x x') is tys
  where
  get-var = maybe-else (fresh-var Γ x) id ∘ is-var-unqual
  x' = fresh-h (renamectxt-in-field ρ) $ get-var ty
  atk' = subst-renamectxt Γ ρ -tk atk
rename-indices-h Γ ρ (Index x atk :: is) [] =
  let x' = fresh-var-renamectxt Γ ρ x in
  Index x' (subst-renamectxt Γ ρ -tk atk) ::
    rename-indices-h (ctxt-var-decl x' Γ) (renamectxt-insert ρ x x') is []
rename-indices-h _ _ [] _ = []

rename-indices : ctxt → indices → 𝕃 tmtp → indices
rename-indices Γ = rename-indices-h Γ empty-renamectxt


tk-erased : tpkd → erased? → erased?
tk-erased (Tkk _) me = Erased
tk-erased (Tkt _) me = me

params-set-erased : erased? → params → params
params-set-erased me = map λ where
  (Param me' x atk) → Param me x atk

args-set-erased : erased? → args → args
args-set-erased = map ∘ arg-set-erased

indices-to-kind : indices → kind → kind
indices-to-kind = flip $ foldr λ {(Index x atk) → KdAbs x atk}

params-to-kind : params → kind → kind
params-to-kind = flip $ foldr λ {(Param me x atk) → KdAbs x atk}

indices-to-tplams : indices → (body : type) → type
indices-to-tplams = flip $ foldr λ where
  (Index x atk) → TpLam x atk

params-to-tplams : params → (body : type) → type
params-to-tplams = flip $ foldr λ where
  (Param me x atk) → TpLam x atk

indices-to-alls : indices → (body : type) → type
indices-to-alls = flip $ foldr λ where
  (Index x atk) → TpAbs Erased x atk

params-to-alls : params → (body : type) → type
params-to-alls = flip $ foldr λ where
  (Param me x atk) → TpAbs (tk-erased atk me) x atk

indices-to-lams : indices → (body : term) → term
indices-to-lams = flip $ foldr λ where
  (Index x atk) → Lam Erased x (just atk)

indices-to-lams' : indices → (body : term) → term
indices-to-lams' = flip $ foldr λ where
  (Index x atk) → Lam Erased x nothing

params-to-lams : params → (body : term) → term
params-to-lams = flip $ foldr λ where
  (Param me x atk) → Lam (tk-erased atk me) x (just atk)

params-to-lams' : params → (body : term) → term
params-to-lams' = flip $ foldr λ where
  (Param me x atk) → Lam (tk-erased atk me) x nothing

indices-to-apps : indices → (body : term) → term
indices-to-apps = flip $ foldl λ where
  (Index x (Tkt T)) t → AppE t (Ttm (Var x))
  (Index x (Tkk k)) t → AppE t (Ttp (TpVar x))

params-to-apps : params → (body : term) → term
params-to-apps = recompose-apps ∘ params-to-args

indices-to-tpapps : indices → (body : type) → type
indices-to-tpapps = flip $ foldl λ where
  (Index x (Tkt _)) T → TpApp T (Ttm (Var x))
  (Index x (Tkk _)) T → TpApp T (Ttp (TpVar x))

params-to-tpapps : params → (body : type) → type
params-to-tpapps = flip apps-type ∘ params-to-args

params-to-caseArgs : params → case-args
params-to-caseArgs = map λ where
  (Param me x (Tkt T)) → CaseArg (if me then CaseArgEr else CaseArgTm) x
  (Param me x (Tkk k)) → CaseArg CaseArgTp x

ctrs-to-lams' : ctrs → (body : term) → term
ctrs-to-lams' = flip $ foldr λ where
  (Ctr x T) → Lam NotErased x nothing

ctrs-to-lams : ctxt → var → params → ctrs → (body : term) → term
ctrs-to-lams Γ x ps cs t = foldr
  (λ {(Ctr y T) f Γ → Lam NotErased y
    (just $ Tkt $ subst Γ (params-to-tpapps ps $ TpVar y) y T)
    $ f $ ctxt-var-decl y Γ})
  (λ Γ → t) cs Γ

add-indices-to-ctxt : indices → ctxt → ctxt
add-indices-to-ctxt = flip $ foldr λ {(Index x atk) → ctxt-var-decl x}

add-params-to-ctxt : params → ctxt → ctxt
add-params-to-ctxt = flip $ foldr λ {(Param me x'' _) → ctxt-var-decl x''}

add-caseArgs-to-ctxt : case-args → ctxt → ctxt
add-caseArgs-to-ctxt = flip $ foldr λ {(CaseArg me x) → ctxt-var-decl x}

add-ctrs-to-ctxt : ctrs → ctxt → ctxt
add-ctrs-to-ctxt = flip $ foldr λ {(Ctr x T) → ctxt-var-decl x}

positivity : Set
positivity = 𝔹 × 𝔹 -- occurs positively × occurs negatively

pattern occurs-nil = ff , ff
pattern occurs-pos = tt , ff
pattern occurs-neg = ff , tt
pattern occurs-all = tt , tt

--positivity-inc : positivity → positivity
--positivity-dec : positivity → positivity
positivity-neg : positivity → positivity
positivity-add : positivity → positivity → positivity

--positivity-inc = map-fst λ _ → tt
--positivity-dec = map-snd λ _ → tt
positivity-neg = uncurry $ flip _,_
positivity-add (+ₘ , -ₘ) (+ₙ , -ₙ) = (+ₘ || +ₙ) , (-ₘ || -ₙ)



-- just tt = negative occurrence; just ff = not in the return type; nothing = okay
{-# TERMINATING #-}
ctr-positive : ctxt → var → type → maybe 𝔹
ctr-positive Γ x = arrs+ Γ ∘ hnf' Γ where
  
  open import conversion

  not-free : ∀ {ed} → ⟦ ed ⟧ → maybe 𝔹
  not-free = maybe-map (λ _ → tt) ∘' maybe-if ∘' is-free-in x

  if-free : ∀ {ed} → ⟦ ed ⟧ → positivity
  if-free t with is-free-in x t
  ...| f = f , f

  if-free-args : args → positivity
  if-free-args as with stringset-contains (free-vars-args as) x
  ...| f = f , f

  hnf' : ctxt → type → type
  hnf' Γ T = hnf Γ unfold-head T

  mtt = maybe-else tt id
  mff = maybe-else ff id

  posₒ = fst
  negₒ = snd
  
  occurs : positivity → maybe 𝔹
  occurs p = maybe-if (negₒ p) >> just tt

  arrs+ : ctxt → type → maybe 𝔹
  type+ : ctxt → type → positivity
  kind+ : ctxt → kind → positivity
  tpkd+ : ctxt → tpkd → positivity
--  tpapp+ : ctxt → type → positivity

  arrs+ Γ (TpAbs me x' atk T) =
    let Γ' = ctxt-var-decl x' Γ in
    occurs (tpkd+ Γ atk) maybe-or arrs+ Γ' (hnf' Γ' T)
  arrs+ Γ (TpApp T tT) = arrs+ Γ T maybe-or (not-free -tT' tT)
--  arrs+ Γ (TpApp T t) = arrs+ Γ T maybe-or not-free t
  arrs+ Γ (TpLam x' atk T) =
    let Γ' = ctxt-var-decl x' Γ in
    occurs (tpkd+ Γ atk) maybe-or arrs+ Γ' (hnf' Γ' T)
  arrs+ Γ (TpVar x') = maybe-if (~ x =string x') >> just ff
  arrs+ Γ T = just ff
  
  type+ Γ (TpAbs me x' atk T) =
    let Γ' = ctxt-var-decl x' Γ in
    positivity-add (positivity-neg $ tpkd+ Γ atk) (type+ Γ' $ hnf' Γ' T)
  type+ Γ (TpIota x' T T') =
    let Γ' = ctxt-var-decl x' Γ; T? = type+ Γ T in
    positivity-add (type+ Γ T) (type+ Γ' T')
  type+ Γ (TpApp T tT) = positivity-add (type+ Γ T) (if-free -tT' tT) -- tpapp+ Γ (TpApp T T')
  --type+ Γ (TpAppt T t) = positivity-add (type+ Γ T) (if-free t) -- tpapp+ Γ (TpAppt T t)
  type+ Γ (TpEq tₗ tᵣ) = occurs-nil
  type+ Γ (TpHole _) = occurs-nil
  type+ Γ (TpLam x' atk T)=
    let Γ' = ctxt-var-decl x' Γ in
    positivity-add (positivity-neg $ tpkd+ Γ atk) (type+ Γ' (hnf' Γ' T))
  type+ Γ (TpVar x') = x =string x' , ff

{-
  tpapp+ Γ T with decompose-tpapps T
  ...| TpVar _ x' , as =
    let f = if-free-args (tmtps-to-args NotErased as) in
    if x =string x'
      then f
      else maybe-else' (data-lookup Γ x' as) f
        λ {(mk-data-info x'' mu asₚ asᵢ ps kᵢ k cs subst-cs) →
          let x''' = fresh-var x'' (ctxt-binds-var Γ) empty-renamectxt
              Γ' = ctxt-var-decl x''' Γ in
          type+ Γ' (hnf' Γ' $ foldr (λ {(Ctr _ cₓ cₜ) → TpArrow cₜ NotErased})
            (mtpvar x''') (subst-cs x'''))}
  ...| _ , _ = if-free T
-}
  
  kind+ Γ (KdAbs x' atk k) =
    let Γ' = ctxt-var-decl x' Γ in
    positivity-add (positivity-neg $ tpkd+ Γ atk) (kind+ Γ' k)
  kind+ Γ _ = occurs-nil

  tpkd+ Γ (Tkt T) = type+ Γ (hnf' Γ T)
  tpkd+ Γ (Tkk k) = kind+ Γ k

