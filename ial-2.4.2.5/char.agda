module char where

open import bool
open import nat
open import eq
open import product
open import product-thms

----------------------------------------------------------------------
-- datatypes
----------------------------------------------------------------------

postulate
  char : Set

{-# BUILTIN CHAR char #-}
{-# COMPILED_TYPE char Char #-}

----------------------------------------------------------------------
-- primitive operations
----------------------------------------------------------------------

private
 primitive
  primCharToNat    : char → ℕ
  primCharEquality : char → char → 𝔹

toNat : char → ℕ
toNat = primCharToNat

infix 4 _=char_

_=char_ : char → char → 𝔹
_=char_ = primCharEquality

postulate
  ≡char-to-= : (c1 c2 : char) → c1 ≡ c2 → _=char_ c1 c2 ≡ tt
  =char-to-≡ : (c1 c2 : char) → _=char_ c1 c2 ≡ tt → c1 ≡ c2

=char-sym : (c1 c2 : char) → (c1 =char c2) ≡ (c2 =char c1)
=char-sym c1 c2 with keep (c1 =char c2)
=char-sym c1 c2 | tt , p rewrite =char-to-≡ c1 c2 p = refl
=char-sym c1 c2 | ff , p with keep (c2 =char c1) 
=char-sym c1 c2 | ff , p | tt , p' rewrite =char-to-≡ c2 c1 p' = refl
=char-sym c1 c2 | ff , p | ff , p' rewrite p | p' = refl

postulate
  _<char_ : char → char → 𝔹
  
{-# COMPILED _<char_ (<)   #-}

----------------------------------------------------------------------
-- defined operations
----------------------------------------------------------------------

-- is a decimal digit
is-digit : char → 𝔹
is-digit '0' = tt
is-digit '1' = tt
is-digit '2' = tt
is-digit '3' = tt
is-digit '4' = tt
is-digit '5' = tt
is-digit '6' = tt
is-digit '7' = tt
is-digit '8' = tt
is-digit '9' = tt
is-digit _ = ff
