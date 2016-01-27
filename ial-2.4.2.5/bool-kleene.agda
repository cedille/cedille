-- Kleene's three-valued logic 

module bool-kleene where

open import bool
open import eq

data 𝔹ₖ : Set where
  tt : 𝔹ₖ
  ff : 𝔹ₖ
  uu : 𝔹ₖ

infix  7 ~ₖ_
infixr 6 _&&ₖ_
infixr 5 _||ₖ_ 
--infixr 4 _impₖ_ 

~ₖ_ : 𝔹ₖ → 𝔹ₖ
~ₖ tt = ff
~ₖ ff = tt
~ₖ uu = uu

-- and
_&&ₖ_ : 𝔹ₖ → 𝔹ₖ → 𝔹ₖ
tt &&ₖ b = b
ff &&ₖ b = ff
uu &&ₖ ff = ff
uu &&ₖ b = uu

-- or
_||ₖ_ : 𝔹ₖ → 𝔹ₖ → 𝔹ₖ
ff ||ₖ b = b
tt ||ₖ b = tt
uu ||ₖ tt = tt
uu ||ₖ b = uu

-- implication
_impₖ_ : 𝔹ₖ → 𝔹ₖ → 𝔹ₖ 
tt impₖ b2 = b2
ff impₖ b2 = tt
uu impₖ tt = tt
uu impₖ b = uu

knownₖ : 𝔹ₖ → 𝔹
knownₖ tt = tt
knownₖ ff = tt
knownₖ uu = ff

to-𝔹 : (b : 𝔹ₖ) → knownₖ b ≡ tt → 𝔹
to-𝔹 tt p = tt
to-𝔹 ff p = ff
to-𝔹 uu () 