module json where

open import lib
open import general-util

mutual
  data json-value : Set where
    json-null : json-value
    json-string : string → json-value
    json-nat : nat → json-value
    json-array : 𝕃 json-value → json-value
    json-object : json → json-value

  data json : Set where
    json-empty : json
    json-pair : json → string → json-value → json

{-# TERMINATING #-}
json-to-rope : json → rope

json-value-to-rope : json-value → rope
json-value-to-rope json-null = [[ "null" ]]
json-value-to-rope (json-string string) = [[ "\"" ]] ⊹⊹ [[ string ]] ⊹⊹ [[ "\"" ]]
json-value-to-rope (json-nat nat) = [[ ℕ-to-string nat ]]
json-value-to-rope (json-array array) = 𝕃-to-rope json-value-to-rope "," array
json-value-to-rope (json-object json) = json-to-rope json

json-to-rope j = [[ "{" ]] ⊹⊹ rec j ⊹⊹ [[ "}" ]] where
  pair-to-rope : string → json-value → rope
  pair-to-rope key value = [[ "\"" ]] ⊹⊹ [[ key ]] ⊹⊹ [[ "\":" ]] ⊹⊹ json-value-to-rope value

  rec : json → rope
  rec json-empty = [[]]
  rec (json-pair json-empty key value) = pair-to-rope key value
  rec (json-pair json key value) = pair-to-rope key value ⊹⊹ [[ "," ]] ⊹⊹ rec json
