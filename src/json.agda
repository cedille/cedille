module json where

open import lib
open import general-util

data json : Set where
  json-null : json
  json-raw : rope → json
  json-string : string → json
  json-nat : nat → json
  json-array : 𝕃 json → json
  json-object : 𝕃 (string × json) → json

json-escape-string : string → string
json-escape-string str = 𝕃char-to-string $ rec $ string-to-𝕃char str where
  rec : 𝕃 char → 𝕃 char
  rec [] = []
  rec ('\b' :: chars) = '\\' :: 'b' :: rec chars
  rec ('\f' :: chars) = '\\' :: 'f' :: rec chars
  rec ('\n' :: chars) = '\\' :: 'n' :: rec chars
  rec ('\r' :: chars) = '\\' :: 'r' :: rec chars
  rec ('\t' :: chars) = '\\' :: 't' :: rec chars
  rec ('"'  :: chars) = '\\' :: '"' :: rec chars
  rec ('\\' :: chars) = '\\' :: '\\' :: rec chars
  rec (char :: chars) = char :: rec chars

{-# TERMINATING #-}
json-to-rope : json → rope
json-to-rope json-null = [[ "null" ]]
json-to-rope (json-raw rope) = rope
json-to-rope (json-string string) = [[ "\"" ]] ⊹⊹ [[ json-escape-string string ]] ⊹⊹ [[ "\"" ]]
json-to-rope (json-nat nat) = [[ ℕ-to-string nat ]]
json-to-rope (json-array array) = [[ "[" ]] ⊹⊹ 𝕃-to-rope json-to-rope "," array ⊹⊹ [[ "]" ]]
json-to-rope (json-object t) = [[ "{" ]] ⊹⊹ 𝕃-to-rope (uncurry λ k v → [[ "\"" ]] ⊹⊹ [[ json-escape-string k ]] ⊹⊹ [[ "\":" ]] ⊹⊹ json-to-rope v)  "," t ⊹⊹ [[ "}" ]]

json-rope : rope → json
json-rope rope = json-raw ([[ "\"" ]] ⊹⊹ rope ⊹⊹ [[ "\"" ]])

json-raw-string : string → json
json-raw-string str = json-raw [[ str ]]

putJson : json → IO ⊤
putJson = putRopeLn ∘ json-to-rope
