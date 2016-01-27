module string-thms where

open import bool
open import eq
open import string

postulate
  =string-refl : (s : string) → s =string s ≡ tt
  =string-to-≡ : (a b : string) → a =string b ≡ tt → a ≡ b

≡string-to-= : (a b : string) → a ≡ b → a =string b ≡ tt
≡string-to-= a .a refl = =string-refl a
