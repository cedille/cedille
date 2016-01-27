-- a simple error monad
module error where

open import level
open import string

infixr 1 _≫=err_ _≫err_

data error-t{ℓ}(A : Set ℓ) : Set ℓ where
  no-error : A → error-t A
  yes-error : string → error-t A

_≫=err_ : ∀{ℓ ℓ'}{A : Set ℓ}{B : Set ℓ'} → error-t A → (A → error-t B) → error-t B
(no-error a) ≫=err f = f a
(yes-error e) ≫=err _ = yes-error e

_≫err_ : ∀{ℓ ℓ'}{A : Set ℓ}{B : Set ℓ'} → error-t A → error-t B → error-t B
a ≫err b = a ≫=err λ _ → b

