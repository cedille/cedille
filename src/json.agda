module json where

open import lib
open import general-util

data json : Set where
  json-null : json
  json-string : string → json
  json-nat : nat → json
  json-array : 𝕃 json → json
  json-object : trie json → json

{-# TERMINATING #-}
json-to-rope : json → rope
json-to-rope json-null = [[ "null" ]]
json-to-rope (json-string string) = [[ "\"" ]] ⊹⊹ [[ string ]] ⊹⊹ [[ "\"" ]]
json-to-rope (json-nat nat) = [[ ℕ-to-string nat ]]
json-to-rope (json-array array) = [[ "[" ]] ⊹⊹ 𝕃-to-rope json-to-rope "," array ⊹⊹ [[ "]" ]]
json-to-rope (json-object t) = [[ "{" ]] ⊹⊹ 𝕃-to-rope key-to-rope "," (trie-strings t) ⊹⊹ [[ "}" ]] where
  key-to-rope : string → rope
  key-to-rope key with trie-lookup t key
  ...| just value = [[ "\"" ]] ⊹⊹ [[ key ]] ⊹⊹ [[ "\":" ]] ⊹⊹ json-to-rope value
  ...| nothing = [[ "\"" ]] ⊹⊹ [[ key ]] ⊹⊹ [[ "\":null" ]] -- shouldn't happen
