{- This file shows a natural attempt to do formatted printing, and where
   that attempt goes wrong.  See string-format.agda for a (working) solution
   to this problem.  -}
module string-format-issue where

open import char
open import eq
open import list
open import nat

open import nat-to-string
open import string

format-th : 𝕃 char → Set
format-th ('%' :: 'n' :: f) = ℕ → format-th f
format-th ('%' :: 's' :: f) = string → format-th f
format-th (c :: f) = format-th f
format-th [] = string

format-t : string → Set
format-t s = format-th (string-to-𝕃char s)

test-format-t : format-t "The %n% %s are %s." ≡ (ℕ → string → string → string)
test-format-t = refl

format-h : 𝕃 char → (f : 𝕃 char) → format-th f
format-h s ('%' :: 'n' :: f) = λ n → format-h (s ++ (string-to-𝕃char (ℕ-to-string n))) f
format-h s ('%' :: 's' :: f) = λ s' → format-h (s ++ (string-to-𝕃char s')) f
format-h s (c :: f) = {!!}
format-h s [] = 𝕃char-to-string s

format : (f : string) → format-t f
format f = format-h [] (string-to-𝕃char f)

