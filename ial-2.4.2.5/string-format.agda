{- formatted printing like printf, except type-safe (as proposed
   in "Cayenne -- a language with dependent types" by Augustsson).

   The types of the rest of the arguments are computed from the
   format string.  -}
module string-format where

open import char
open import eq
open import list
open import nat

open import nat-to-string
open import string

{- We will first convert the format string to the following type,
   so we can avoid default cases in the definition of format-th
   (cf. string-format-issue.agda). -}
data format-d : Set where
  format-nat : format-d → format-d
  format-string : format-d → format-d
  not-format : (c : char) → format-d → format-d
  empty-format : format-d

format-cover : 𝕃 char → format-d
format-cover ('%' :: 'n' :: s) = format-nat (format-cover s)
format-cover ('%' :: 's' :: s) = format-string (format-cover s)
format-cover (c :: s) = not-format c (format-cover s)
format-cover [] = empty-format

format-th : format-d → Set
format-th (format-nat v) = ℕ → format-th v
format-th (format-string v) = string → format-th v
format-th (not-format c v) = format-th v
format-th empty-format = string

format-t : string → Set
format-t s = format-th (format-cover (string-to-𝕃char s))

format-h : 𝕃 char → (d : format-d) → format-th d
format-h s (format-nat v) = λ n → format-h (s ++ (string-to-𝕃char (ℕ-to-string n))) v
format-h s (format-string v) = λ s' → format-h (s ++ (string-to-𝕃char s')) v
format-h s (not-format c v) = format-h (s ++ [ c ] ) v
format-h s empty-format = 𝕃char-to-string s

format : (f : string) → format-t f
format f = format-h [] (format-cover (string-to-𝕃char f))

format-type-test : Set
format-type-test = format-t "%n% of the %ss are in the %s %s"

format-test : string
format-test = format "%n% of the %ss are in the %s %s" 25 "dog" "toasty" "doghouse"

format-test-lem : format-test ≡ "25% of the dogs are in the toasty doghouse"
format-test-lem = refl