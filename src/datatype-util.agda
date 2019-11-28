module datatype-util where
open import constants
open import ctxt
open import syntax-util
open import general-util
open import type-util
open import cedille-types
open import subst
open import rename
open import free-vars

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
  x' = fresh-var-renamectxt Γ ρ (maybe-else x id (is-var-unqual ty))
  atk' = subst-renamectxt Γ ρ -tk atk
rename-indices-h Γ ρ (Index x atk :: is) [] =
  let x' = fresh-var-renamectxt Γ ρ x in
  Index x' (subst-renamectxt Γ ρ -tk atk) ::
    rename-indices-h (ctxt-var-decl x' Γ) (renamectxt-insert ρ x x') is []
rename-indices-h _ _ [] _ = []

rename-indices : ctxt → indices → 𝕃 tmtp → indices
rename-indices Γ = rename-indices-h Γ empty-renamectxt

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
module positivity (x : var) where
  
  open import conversion

  not-free : ∀ {ed} → ⟦ ed ⟧ → maybe 𝔹
  not-free = maybe-map (λ _ → tt) ∘' maybe-if ∘' is-free-in x

  if-free : ∀ {ed} → ⟦ ed ⟧ → positivity
  if-free t with is-free-in x t
  ...| f = f , f

  if-free-args : args → positivity
  if-free-args as with stringset-contains (free-vars-args as) x
  ...| f = f , f

  hnf' : ∀ {ed} → ctxt → ⟦ ed ⟧ → ⟦ ed ⟧
  hnf' Γ T = hnf Γ unfold-no-defs T

  mtt = maybe-else tt id
  mff = maybe-else ff id

  posₒ = fst
  negₒ = snd
  
  occurs : positivity → maybe 𝔹
  occurs p = maybe-if (negₒ p) >> just tt

  {-# TERMINATING #-}
  arrs+ : ctxt → type → maybe 𝔹
  type+ : ctxt → type → positivity
  kind+ : ctxt → kind → positivity
  tpkd+ : ctxt → tpkd → positivity
  tpapp+ : ctxt → type → positivity

  arrs+ Γ (TpAbs me x' atk T) =
    let Γ' = ctxt-var-decl x' Γ in
    occurs (tpkd+ Γ $ hnf' Γ -tk atk) ||-maybe arrs+ Γ' (hnf' Γ' T)
  arrs+ Γ (TpApp T tT) = occurs (tpapp+ Γ $ hnf' Γ (TpApp T tT))
                       --arrs+ Γ T maybe-or (not-free -tT' tT)
  arrs+ Γ (TpLam x' atk T) =
    let Γ' = ctxt-var-decl x' Γ in
    occurs (tpkd+ Γ $ hnf' Γ -tk atk) ||-maybe arrs+ Γ' (hnf' Γ' T)
  arrs+ Γ (TpVar x') = maybe-if (~ x =string x') >> just ff
  arrs+ Γ T = just ff
  
  type+ Γ (TpAbs me x' atk T) =
    let Γ' = ctxt-var-decl x' Γ in
    positivity-add (positivity-neg $ tpkd+ Γ $ hnf' Γ -tk atk) (type+ Γ' $ hnf' Γ' T)
  type+ Γ (TpIota x' T T') =
    let Γ' = ctxt-var-decl x' Γ in
    positivity-add (type+ Γ $ hnf' Γ T) (type+ Γ' $ hnf' Γ' T')
  type+ Γ (TpApp T tT) = tpapp+ Γ $ hnf' Γ $ TpApp T tT
  type+ Γ (TpEq tₗ tᵣ) = occurs-nil
  type+ Γ (TpHole _) = occurs-nil
  type+ Γ (TpLam x' atk T)=
    let Γ' = ctxt-var-decl x' Γ in
    positivity-add (positivity-neg $ tpkd+ Γ $ hnf' Γ -tk atk) (type+ Γ' (hnf' Γ' T))
  type+ Γ (TpVar x') = x =string x' , ff

  tpapp+ Γ T with decompose-tpapps T
  ...| TpVar x' , as =
    let f = if-free-args (tmtps-to-args NotErased as) in
    if x =string x'
      then positivity-add occurs-pos f
      else maybe-else' (data-lookup Γ x' as) f
        λ {(mk-data-info x'' xₒ'' asₚ asᵢ ps kᵢ k cs csₚₛ eds gds) →
          type+ Γ (hnf' Γ $ TpAbs tt x'' (Tkk k) $ foldr (uncurry λ cₓ cₜ → TpAbs ff ignored-var (Tkt cₜ)) (TpVar x'') (inst-ctrs Γ ps asₚ cs))}
  ...| _ , _ = if-free T

  
  kind+ Γ (KdAbs x' atk k) =
    let Γ' = ctxt-var-decl x' Γ in
    positivity-add (positivity-neg $ tpkd+ Γ $ hnf' Γ -tk atk) (kind+ Γ' k)
  kind+ Γ _ = occurs-nil

  tpkd+ Γ (Tkt T) = type+ Γ (hnf' Γ T)
  tpkd+ Γ (Tkk k) = kind+ Γ k

  ctr-positive : ctxt → type → maybe 𝔹
  ctr-positive Γ = arrs+ Γ ∘ hnf' Γ
