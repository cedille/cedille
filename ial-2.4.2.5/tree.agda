module tree where

open import bool
open import eq
open import level
open import list 
open import list-to-string 
open import nat
open import nat-thms
open import string

----------------------------------------------------------------------
-- datatype
----------------------------------------------------------------------

-- nonempty trees
data 𝕋 {ℓ} (A : Set ℓ) : Set ℓ where
  node : A → 𝕃 (𝕋 A) → 𝕋 A

----------------------------------------------------------------------
-- tree operations
----------------------------------------------------------------------

leaf : ∀ {ℓ}{A : Set ℓ} → A → 𝕋 A
leaf a = node a []

𝕋-to-string : ∀ {ℓ}{A : Set ℓ} → (f : A → string) → (t : 𝕋 A) → string
𝕋s-to-string : ∀ {ℓ}{A : Set ℓ} → (f : A → string) → (ts : 𝕃 (𝕋 A)) → string
𝕋-to-string f (node a []) = f a
𝕋-to-string f (node a ts) = "(" ^ (f a) ^ (𝕋s-to-string f ts) ^ ")"
𝕋s-to-string f [] = ""
𝕋s-to-string f (t :: ts) = " " ^ (𝕋-to-string f t) ^ (𝕋s-to-string f ts)

perfect-binary-tree : ∀ {ℓ}{A : Set ℓ} → ℕ → A → 𝕋 A
perfect-binary-tree 0 a = (node a [])
perfect-binary-tree (suc n) a = let t = perfect-binary-tree n a in 
                                  (node a (t :: t :: []))

size𝕋 : ∀ {ℓ}{A : Set ℓ} → 𝕋 A → ℕ
size𝕋s : ∀ {ℓ}{A : Set ℓ} → 𝕃 (𝕋 A) → ℕ
size𝕋 (node a ts) = suc (size𝕋s ts)
size𝕋s [] = 0
size𝕋s (t :: ts) = size𝕋 t + size𝕋s ts

size-perfect : ∀ {ℓ}{A : Set ℓ}(n : ℕ)(a : A) → (size𝕋 (perfect-binary-tree n a)) ≡ pred (2 pow (suc n))
size-perfect 0 a = refl
size-perfect (suc n) a with (size𝕋 (perfect-binary-tree n a)) | size-perfect n a
... | s | ps rewrite ps with 2 pow n | nonzero-pow 2 n refl
... | x | px rewrite +0 x with x + x | (iszerosum2 x x px)
... | x2 | q rewrite +0 x2 | +0 (pred x2) | sym (+suc (pred x2) (pred x2)) | sucpred q | pred+ x2 x2 q = refl
