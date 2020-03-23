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

data ctorCheckT : Set where
  ctorOk : ctorCheckT
  ctorNotInReturnType : ctorCheckT
  ctorNegative : ctorCheckT

posₒ = fst
negₒ = snd
  
occurs : positivity → ctorCheckT
occurs p = if (negₒ p) then ctorNegative else ctorOk

or-ctorCheckT : ctorCheckT → ctorCheckT → ctorCheckT 
or-ctorCheckT ctorOk r = r
or-ctorCheckT ctorNegative  _ = ctorNegative
or-ctorCheckT ctorNotInReturnType _ = ctorNotInReturnType

posM : Set → Set
posM A = 𝕃 tpkd → A × 𝕃 tpkd

run-posM : ∀{A : Set} → posM A → A × 𝕃 tpkd
run-posM p = p []

extract-pos : ∀{A : Set} → posM A → A
extract-pos = fst ∘ run-posM

instance
  posM-monad : monad posM
  return ⦃ posM-monad ⦄ a = λ l → a , l
  _>>=_ ⦃ posM-monad ⦄ p ap l with p l 
  _>>=_ ⦃ posM-monad ⦄ p ap l | a , l' = ap a l'

  posM-functor : functor posM
  fmap ⦃ posM-functor ⦄ g m l with m l
  fmap ⦃ posM-functor ⦄ g m l | a , l' = g a , l'

  posM-applicative : applicative posM
  pure ⦃ posM-applicative ⦄ = return
  _<*>_ ⦃ posM-applicative ⦄ mab ma l with mab l
  _<*>_ ⦃ posM-applicative ⦄ mab ma l | f , l' with ma l'
  _<*>_ ⦃ posM-applicative ⦄ mab ma l | f , l' | a , l'' = 
    f a , l''

add-posM : tpkd → posM ⊤
add-posM x = λ l → triv , x :: l

module positivity (x : var) where
  
  open import conversion ff using (hnf ; unfold-no-defs)

  if-free : ∀ {ed} → ⟦ ed ⟧ → positivity
  if-free t with is-free-in x t
  ...| f = f , f

  if-free-args : args → positivity
  if-free-args as =
    let c = stringset-contains (free-vars-args as) x in c , c

  hnf' : ∀ {ed} → ctxt → ⟦ ed ⟧ → ⟦ ed ⟧
  hnf' Γ T = hnf Γ unfold-no-defs T

  mtt = maybe-else tt id
  mff = maybe-else ff id

  {-# TERMINATING #-}
  type+ : ctxt → type → posM positivity
  kind+ : ctxt → kind → posM positivity
  tpkd+ : ctxt → tpkd → posM positivity
  tpapp+ : ctxt → type → posM positivity
  type+h : ctxt → type → posM positivity
  kind+h : ctxt → kind → posM positivity
  tpkd+h : ctxt → tpkd → posM positivity
  tpapp+h : ctxt → type → posM positivity

  type+ Γ T = type+h Γ T -- >>= λ p → add-posM (Tkt T) >> return p
  kind+ Γ k = kind+h Γ k
  tpkd+ Γ x = tpkd+h Γ x
  tpapp+ Γ T = tpapp+h Γ T

  type+h Γ (TpAbs me x' atk T) =
    let Γ' = ctxt-var-decl x' Γ in
      pure positivity-add <*>
        (fmap positivity-neg $ tpkd+ Γ $ hnf' Γ -tk atk) <*>
        (type+ Γ' $ hnf' Γ' T)
  type+h Γ (TpIota x' T T') =
    let Γ' = ctxt-var-decl x' Γ in
      pure positivity-add <*>
        (type+ Γ $ hnf' Γ T) <*>
        (type+ Γ' $ hnf' Γ' T')
  type+h Γ (TpApp T tT) = tpapp+ Γ $ hnf' Γ $ TpApp T tT
  type+h Γ (TpEq tₗ tᵣ) = pure occurs-nil
  type+h Γ (TpHole _) = pure occurs-nil
  type+h Γ (TpLam x' atk T)=
    let Γ' = ctxt-var-decl x' Γ in
      pure positivity-add <*>
        (fmap positivity-neg $ tpkd+ Γ $ hnf' Γ -tk atk) <*>
        (type+ Γ' (hnf' Γ' T))
  type+h Γ (TpVar x') = pure $ x =string x' , ff

  kind+h Γ (KdAbs x' atk k) =
    let Γ' = ctxt-var-decl x' Γ in
      pure positivity-add <*>
      (fmap positivity-neg $ tpkd+ Γ $ hnf' Γ -tk atk) <*>
      (kind+ Γ' k)
  kind+h Γ _ = pure occurs-nil

  tpkd+h Γ (Tkt T) = type+ Γ (hnf' Γ T)
  tpkd+h Γ (Tkk k) = kind+ Γ k

  tpapp+h Γ T with decompose-tpapps T
  tpapp+h Γ T | TpVar x' , as =
    let f = if-free-args (tmtps-to-args NotErased as) in
    if x =string x'
      then pure (positivity-add occurs-pos f)
      else maybe-else' (data-lookup Γ x' as) (pure f)
        λ {(mk-data-info x'' xₒ'' asₚ asᵢ ps kᵢ k cs csₚₛ eds gds) →
          let s = (inst-type Γ ps asₚ (hnf' Γ $ TpAbs tt x'' (Tkk k) $ foldr (uncurry λ cₓ cₜ → TpAbs ff ignored-var (Tkt cₜ)) (TpVar x'') cs)) in
          add-posM (Tkt s) >>
          type+ Γ s }
  tpapp+h Γ T | _ , _ = pure $ if-free T

  {-# TERMINATING #-}
  arrs+ : ctxt → type → posM ctorCheckT

  arrs+ Γ (TpAbs me x' atk T) =
    let Γ' = ctxt-var-decl x' Γ in
     pure or-ctorCheckT <*>
       (fmap occurs (tpkd+ Γ $ hnf' Γ -tk atk)) <*>
       (arrs+ Γ' (hnf' Γ' T))
  arrs+ Γ (TpApp T tT) = fmap occurs (tpapp+ Γ $ hnf' Γ (TpApp T tT))
  arrs+ Γ (TpLam x' atk T) =
    let Γ' = ctxt-var-decl x' Γ in
      pure or-ctorCheckT <*>
        (fmap occurs (tpkd+ Γ $ hnf' Γ -tk atk)) <*>
        (arrs+ Γ' (hnf' Γ' T))
  arrs+ Γ (TpVar x') = return $ if (x =string x') then ctorOk else ctorNotInReturnType

  arrs+ _ _ = return ctorNegative

  ctr-positive : ctxt → type → posM ctorCheckT
  ctr-positive Γ = (arrs+ Γ ∘ hnf' Γ)

-- build the evidence for a sigma-term, given datatype X with associated info μ
sigma-build-evidence : var → datatype-info → term
sigma-build-evidence X μ =
  if datatype-info.name μ =string X then recompose-apps (datatype-info.asₚ μ) (Var (data-is/ X)) else Var (mu-isType/' X)

