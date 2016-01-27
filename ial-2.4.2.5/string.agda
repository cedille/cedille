module string where

open import bool
open import eq
open import char
open import list
open import nat
open import unit

----------------------------------------------------------------------
-- datatypes
----------------------------------------------------------------------

postulate
  string : Set

{-# BUILTIN STRING string #-}
{-# COMPILED_TYPE string String #-}

private
 primitive
  primStringToList   : string → 𝕃 char
  primStringAppend   : string → string → string
  primStringFromList : 𝕃 char → string
  primStringEquality : string → string → 𝔹

-- see string-thms.agda for some axioms about the above primitive functions

----------------------------------------------------------------------
-- syntax
----------------------------------------------------------------------

infixr 6 _^_ 
infix 8 _=string_



----------------------------------------------------------------------
-- operations
----------------------------------------------------------------------

_^_ : string → string → string
_^_ = primStringAppend

string-to-𝕃char : string → 𝕃 char
string-to-𝕃char = primStringToList

𝕃char-to-string : 𝕃 char → string
𝕃char-to-string = primStringFromList

_=string_ : string → string → 𝔹
_=string_ = primStringEquality


char-to-string : char → string
char-to-string c = 𝕃char-to-string [ c ]

string-append-t : ℕ → Set
string-append-t 0 = string → string 
string-append-t (suc n) = string → (string-append-t n)

string-append-h : (n : ℕ) → string → string-append-t n
string-append-h 0 ret = λ x → ret ^ x
string-append-h (suc n) ret = λ x → (string-append-h n (ret ^ x))

string-append : (n : ℕ) → string-append-t n
string-append n = string-append-h n ""

string-concat : 𝕃 string → string
string-concat [] = ""
string-concat (s :: ss) = s ^ (string-concat ss)

string-concat-sep : (separator : string) → 𝕃 string → string
string-concat-sep sep [] = ""
string-concat-sep sep (s1 :: ss) with ss
... | [] = s1
... | s2 :: ss' = s1 ^ sep ^ (string-concat-sep sep ss)

string-concat-sep-map : ∀{A : Set} → (separator : string) → (A → string) → 𝕃 A → string
string-concat-sep-map sep f l = string-concat-sep sep (map f l)

escape-string-h : 𝕃 char → 𝕃 char
escape-string-h ('\n' :: cs) = '\\' :: 'n' :: (escape-string-h cs)
escape-string-h ('"' :: cs) = '\\' :: '"' :: (escape-string-h cs)
escape-string-h (c :: cs) = c :: escape-string-h cs
escape-string-h [] = []

escape-string : string → string
escape-string s = 𝕃char-to-string( escape-string-h( string-to-𝕃char s ) )

string-length : string → ℕ
string-length s = length (string-to-𝕃char s)
