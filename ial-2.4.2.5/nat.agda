module nat where

open import product
open import bool

----------------------------------------------------------------------
-- datatypes
----------------------------------------------------------------------

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

nat = ℕ

----------------------------------------------------------------------
-- syntax
----------------------------------------------------------------------

infixl 10 _*_
infixl 9 _+_ _∸_
infixl 8 _<_ _=ℕ_ _≤_ _>_ _≥_

-- pragmas to get decimal notation:

{-# BUILTIN NATURAL ℕ #-}

----------------------------------------------------------------------
-- operations
----------------------------------------------------------------------

---------------------------------------
-- basic arithmetic operations
---------------------------------------

_+_ : ℕ → ℕ → ℕ
zero  + n = n
suc m + n = suc (m + n)

{-# BUILTIN NATPLUS _+_ #-}

_*_ : ℕ → ℕ → ℕ
zero  * n = zero
suc m * n = n + (m * n)

{-# BUILTIN NATTIMES _*_ #-}

pred : ℕ → ℕ
pred 0 = 0
pred (suc n) = n

_∸_ : ℕ → ℕ → ℕ
m     ∸ zero  = m
zero  ∸ suc n = zero
suc m ∸ suc n = m ∸ n

-- see nat-division.agda for division function

{-# BUILTIN NATMINUS _∸_ #-}

square : ℕ → ℕ
square x = x * x

--------------------------------------------------
-- comparisons
--------------------------------------------------

_<_ : ℕ → ℕ → 𝔹
0 < 0 = ff
0 < (suc y) = tt
(suc x) < (suc y) = x < y
(suc x) < 0 = ff

_=ℕ_ : ℕ → ℕ → 𝔹
0 =ℕ 0 = tt
suc x =ℕ suc y = x =ℕ y
_ =ℕ _ = ff

_≤_ : ℕ → ℕ → 𝔹
x ≤ y = (x < y) || x =ℕ y

_>_ : ℕ → ℕ → 𝔹
a > b = b < a

_≥_ : ℕ → ℕ → 𝔹
a ≥ b = b ≤ a

min : ℕ → ℕ → ℕ
min x y = if x < y then x else y

max : ℕ → ℕ → ℕ
max x y = if x < y then y else x

data compare-t : Set where
  compare-lt : compare-t
  compare-eq : compare-t
  compare-gt : compare-t

compare : ℕ → ℕ → compare-t
compare 0 0 = compare-eq
compare 0 (suc y) = compare-lt
compare (suc x) 0 = compare-gt
compare (suc x) (suc y) = compare x y 

iszero : ℕ → 𝔹
iszero 0 = tt
iszero _ = ff

parity : ℕ → 𝔹
parity 0 = ff
parity (suc x) = ~ (parity x)

_pow_ : ℕ → ℕ → ℕ
x pow 0 = 1
x pow (suc y) = x * (x pow y)

factorial : ℕ → ℕ
factorial 0 = 1
factorial (suc x) = (suc x) * (factorial x)

is-even : ℕ → 𝔹
is-odd : ℕ → 𝔹
is-even 0 = tt
is-even (suc x) = is-odd x
is-odd 0 = ff
is-odd (suc x) = is-even x
