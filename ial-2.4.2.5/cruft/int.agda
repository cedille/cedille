module int where

open import bool
open import eq
open import nat
open import product

----------------------------------------------------------------------
-- datatypes
----------------------------------------------------------------------

data pol : Set where
  pos : pol
  neg : pol

data sign : Set where
  nonzero : pol → sign
  zero : sign

data int : sign → Set where
  +0 : int zero
  unit : ∀ {p : pol} → int (nonzero p)
  next_ : ∀ {p : pol} → int (nonzero p) → int (nonzero p)
  
data nonneg : sign → Set where
  pos-nonneg : nonneg (nonzero pos)
  zero-nonneg : nonneg zero

data nonpos : sign → Set where
  neg-nonpos : nonpos (nonzero neg)
  zero-nonpos : nonpos zero

ℤ = Σi sign int

ℤ-≥-0 = Σi sign (λ s → nonneg s × int s)

ℤ-≤-0 = Σi sign (λ s → nonpos s × int s)

----------------------------------------------------------------------
-- syntax
----------------------------------------------------------------------

infixl 6 _+ℤ_

----------------------------------------------------------------------
-- operations
----------------------------------------------------------------------

eq-pol : pol → pol → 𝔹
eq-pol pos pos = tt
eq-pol neg neg = tt
eq-pol pos neg = ff
eq-pol neg pos = ff

{- add a unit with the given polarity to the given int (so if the polarity
   is pos we are adding one, if it is neg we are subtracting one).
   Return the new int, together with its sign, which could change. -}
add-unit : pol → ∀{s : sign} → int s → ℤ
add-unit p +0 = , unit{p}
add-unit p (unit{p'}) = if eq-pol p p' then , next (unit{p}) else , +0
add-unit p (next_{p'} x) = if eq-pol p p' then , next (next x) else , x

_+ℤ_ : ℤ → ℤ → ℤ 
(, +0) +ℤ (, x) = , x
(, x) +ℤ (, +0) = , x
(, x) +ℤ (, unit{p}) = add-unit p x
(, unit{p}) +ℤ (, x) = add-unit p x
(, next_{p} x) +ℤ (, next_{p'} y) with ((, x) +ℤ (, next y))
... | , r = add-unit p r

ℕ-to-ℤ : ℕ → ℤ-≥-0
ℕ-to-ℤ zero = , (zero-nonneg , +0)
ℕ-to-ℤ (suc x) with ℕ-to-ℤ x
... | , (zero-nonneg , y) = , ( pos-nonneg , unit )
... | , (pos-nonneg , y) = , ( pos-nonneg , next y)

