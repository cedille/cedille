module maybe where

open import level
open import eq
open import bool

----------------------------------------------------------------------
-- datatypes
----------------------------------------------------------------------

data maybe {ℓ}(A : Set ℓ) : Set ℓ where
  just : A → maybe A
  nothing : maybe A

----------------------------------------------------------------------
-- operations
----------------------------------------------------------------------

_≫=maybe_ : ∀ {ℓ}{A B : Set ℓ} → maybe A → (A → maybe B) → maybe B
nothing ≫=maybe f = nothing
(just x) ≫=maybe f = f x

return-maybe : ∀ {ℓ}{A : Set ℓ} → A → maybe A
return-maybe a = just a

down-≡ : ∀{ℓ}{A : Set ℓ}{a a' : A} → just a ≡ just a' → a ≡ a'
down-≡ refl = refl

isJust : ∀{ℓ}{A : Set ℓ} → maybe A → 𝔹
isJust nothing = ff
isJust (just _) = tt

maybe-extract : ∀{ℓ}{A : Set ℓ} → (x : maybe A) → isJust x ≡ tt → A
maybe-extract (just x) p = x
maybe-extract nothing ()

maybe-map : ∀{ℓ}{A B : Set ℓ} → (A → B) → maybe A → maybe B
maybe-map f (just x) = just (f x)
maybe-map f nothing = nothing