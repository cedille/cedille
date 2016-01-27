module nat-to-string where

open import bool
open import char
open import eq
open import list
open import maybe
open import nat
open import nat-division
open import nat-thms
open import product
open import string
open import termination

ℕ-to-digitsh : (base : ℕ) → 1 < base ≡ tt → (x : ℕ) → ↓𝔹 _>_ x → 𝕃 ℕ
ℕ-to-digitsh _ _ 0 _ = []
ℕ-to-digitsh base bp (suc x) (pf↓ fx) with (suc x) ÷ base ! (<=ℕff2 base bp)
... | q , r , p , _ = r :: (ℕ-to-digitsh base bp q (fx (÷<{base}{q}{r}{x} bp p)))

ℕ-to-digits : ℕ → 𝕃 ℕ
ℕ-to-digits x = reverse (ℕ-to-digitsh 10 refl x (↓-> x))

digit-to-string : ℕ → string
digit-to-string 0 = "0"
digit-to-string 1 = "1"
digit-to-string 2 = "2"
digit-to-string 3 = "3"
digit-to-string 4 = "4"
digit-to-string 5 = "5"
digit-to-string 6 = "6"
digit-to-string 7 = "7"
digit-to-string 8 = "8"
digit-to-string 9 = "9"
digit-to-string _ = "unexpected-digit"

digits-to-string : 𝕃 ℕ → string
digits-to-string [] = ""
digits-to-string (d :: ds) = (digit-to-string d) ^ (digits-to-string ds)

ℕ-to-string : ℕ → string
ℕ-to-string 0 = "0"
ℕ-to-string (suc x) = digits-to-string (ℕ-to-digits (suc x))

string-to-digit : char → maybe ℕ 
string-to-digit '0' = just 0
string-to-digit '1' = just 1
string-to-digit '2' = just 2
string-to-digit '3' = just 3
string-to-digit '4' = just 4
string-to-digit '5' = just 5
string-to-digit '6' = just 6
string-to-digit '7' = just 7
string-to-digit '8' = just 8
string-to-digit '9' = just 9
string-to-digit _ = nothing

-- the digits are in order from least to most significant
digits-to-ℕh : ℕ → ℕ → 𝕃 ℕ → ℕ
digits-to-ℕh multiplier sum [] = sum
digits-to-ℕh multiplier sum (x :: xs) = digits-to-ℕh (10 * multiplier) (x * multiplier + sum) xs

digits-to-ℕ : 𝕃 ℕ → ℕ
digits-to-ℕ digits = digits-to-ℕh 1 0 digits

string-to-ℕ : string → maybe ℕ
string-to-ℕ s with 𝕃maybe-map string-to-digit (reverse (string-to-𝕃char s)) 
... | nothing = nothing
... | just ds = just (digits-to-ℕ ds)
