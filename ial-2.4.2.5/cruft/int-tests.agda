module int-tests where

open import int
open import eq
open import product

three : ℤ
three = , next next unit{pos}

-two : ℤ
-two = , next unit{neg}

one = -two +ℤ three

one-lem : one ≡ ,_ { a = nonzero pos } unit
one-lem = refl

six = three +ℤ three

-four = -two +ℤ -two

