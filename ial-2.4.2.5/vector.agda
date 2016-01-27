module vector where

open import bool
open import eq
open import list
open import list-to-string
open import nat
open import nat-thms
open import product
open import string

----------------------------------------------------------------------
-- datatypes
----------------------------------------------------------------------

data 𝕍 {ℓ} (A : Set ℓ) : ℕ → Set ℓ where
  [] : 𝕍 A 0
  _::_ : {n : ℕ} → A → 𝕍 A n → 𝕍 A (suc n)

vector = 𝕍

----------------------------------------------------------------------
-- syntax
----------------------------------------------------------------------

infixr 6 _::_ _++𝕍_

----------------------------------------------------------------------
-- operations
----------------------------------------------------------------------

[_]𝕍 : ∀ {ℓ} {A : Set ℓ} → A → 𝕍 A 1
[ x ]𝕍 = x :: []

_++𝕍_ : ∀ {ℓ} {A : Set ℓ}{n m : ℕ} → 𝕍 A n → 𝕍 A m → 𝕍 A (n + m)
[]        ++𝕍 ys = ys
(x :: xs) ++𝕍 ys = x :: xs ++𝕍 ys

head𝕍 : ∀ {ℓ} {A : Set ℓ}{n : ℕ} → 𝕍 A (suc n) → A
head𝕍 (x :: _) = x

tail𝕍 : ∀ {ℓ} {A : Set ℓ}{n : ℕ} → 𝕍 A n → 𝕍 A (pred n)
tail𝕍 [] = []
tail𝕍 (_ :: xs) = xs

map𝕍 : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'}{n : ℕ} → (A → B) → 𝕍 A n → 𝕍 B n
map𝕍 f []       = []
map𝕍 f (x :: xs) = f x :: map𝕍 f xs

concat𝕍 : ∀{ℓ}{A : Set ℓ}{n m : ℕ} → 𝕍 (𝕍 A n) m → 𝕍 A (m * n)
concat𝕍 [] = []
concat𝕍 (x :: xs) = x ++𝕍 (concat𝕍 xs)

nth𝕍 : ∀ {ℓ} {A : Set ℓ}{m : ℕ} → (n : ℕ) → n < m ≡ tt → 𝕍 A m → A
nth𝕍 0 _ (x :: _) = x
nth𝕍 (suc n) p (_ :: xs) = nth𝕍 n p xs
nth𝕍 (suc n) () []
nth𝕍 0 () []

repeat𝕍 : ∀ {ℓ} {A : Set ℓ} → (a : A)(n : ℕ) → 𝕍 A n
repeat𝕍 a 0 = []
repeat𝕍 a (suc n) = a :: (repeat𝕍 a n)

foldl𝕍 : ∀{ℓ ℓ'}{A : Set ℓ}{B : Set ℓ'} → B → (B → A → B) → {n : ℕ} → 𝕍 A n → 𝕍 B n
foldl𝕍 b _f_ [] = []
foldl𝕍 b _f_ (x :: xs) = let r = (b f x) in r :: (foldl𝕍 r _f_  xs)

zipWith𝕍 : ∀ {ℓ ℓ' ℓ''} {A : Set ℓ}{B : Set ℓ'}{C : Set ℓ''} → 
           (A → B → C) → {n : ℕ} → 𝕍 A n → 𝕍 B n → 𝕍 C n
zipWith𝕍 f [] [] = []
zipWith𝕍 _f_ (x :: xs) (y :: ys) = (x f y) :: (zipWith𝕍 _f_ xs ys)

-- helper function for all𝕍
allh𝕍 : ∀ {ℓ} {A : Set ℓ}{n : ℕ}(p : ℕ → A → 𝔹) → 𝕍 A n → ℕ → 𝔹
allh𝕍 p [] n = tt
allh𝕍 p (x :: xs) n = p n x && allh𝕍 p xs (suc n)

-- given a predicate p which takes in an index and the element of 
-- the given 𝕍 at that index, return tt iff the predicate
-- returns true for all indices (and their elements).
all𝕍 : ∀ {ℓ} {A : Set ℓ}{n : ℕ}(p : ℕ → A → 𝔹) → 𝕍 A n → 𝔹
all𝕍 p v = allh𝕍 p v 0

𝕍-to-𝕃 : ∀ {ℓ} {A : Set ℓ}{n : ℕ} → 𝕍 A n → 𝕃 A
𝕍-to-𝕃 [] = []
𝕍-to-𝕃 (x :: xs) = x :: (𝕍-to-𝕃 xs)

𝕃-to-𝕍 : ∀ {ℓ} {A : Set ℓ} → 𝕃 A → Σ ℕ (λ n → 𝕍 A n)
𝕃-to-𝕍 [] = (0 , [])
𝕃-to-𝕍 (x :: xs) with 𝕃-to-𝕍 xs
... | (n , v) = (suc n , x :: v)

{- turn the given 𝕍 into a string by calling f on each element, and separating the elements
   with the given separator string -}
𝕍-to-string : ∀ {ℓ} {A : Set ℓ}{n : ℕ} → (f : A → string) → (separator : string) → 𝕍 A n → string
𝕍-to-string f sep v = 𝕃-to-string f sep (𝕍-to-𝕃 v)

