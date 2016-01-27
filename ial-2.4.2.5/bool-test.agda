module bool-test where

open import bool
open import eq
open import level

~~tt : ~ ~ tt ≡ tt
~~tt = refl

~~ff : ~ ~ ff ≡ ff
~~ff = refl

~~-elim2 : ∀ (b : 𝔹) → ~ ~ b ≡ b
~~-elim2 tt = ~~tt
~~-elim2 ff = ~~ff

~~tt' : ~ ~ tt ≡ tt
~~tt' = refl{lzero}{𝔹}{tt}

~~ff' : ~ ~ ff ≡ ff
~~ff' = refl{lzero}{𝔹}{ff}

test1 : 𝔹
test1 = tt && ff

test2 : 𝔹
test2 = tt && tt

test1-ff : test1 ≡ ff
test1-ff = refl

test2-tt : test2 ≡ tt
test2-tt = refl
