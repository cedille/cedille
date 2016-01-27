module list-to-string where

open import list
open import string

𝕃-to-string : ∀ {ℓ} {A : Set ℓ} → (f : A → string) → (separator : string) → 𝕃 A → string
𝕃-to-string f sep [] = ""
𝕃-to-string f sep (x1 :: (x2 :: xs)) = (f x1) ^ sep ^ (𝕃-to-string f sep (x2 :: xs))
𝕃-to-string f sep (x1 :: []) = (f x1) 
