import cedille-options
module write-html-util (options : cedille-options.options) where
open import json
-- below imports are just what copied from elab-util
open import general-util
open import cedille-types
open import syntax-util
open import type-util
open import ctxt
open import conversion
open import constants
open import instances
open import subst
open import rename
open import rewriting
open import free-vars
open import toplevel-state options {IO}
open import datatype-util
open import bohm-out

-- TODO:
-- recursively traverse all dependencies
-- generate dependency link
-- escape html special characters

print-list-of-strings : 𝕃 string → IO ⊤
print-list-of-strings [] = putStrLn ""
print-list-of-strings (hd :: tl) = (putStrLn hd) >> print-list-of-strings tl

new-deps : 𝕃 filepath → 𝕃 filepath → 𝕃 filepath
new-deps ds old = foldr' ds (λ a ds → remove general-util._=string_  a ds) old

-- Basically a BFS. Each time fm is checked for new neighbours. A neighbour should be picked out while the rest be stuffed in store.
{-# NON_TERMINATING #-}
get-all-deps-h : toplevel-state → filepath → 𝕃 filepath →  𝕃 filepath →  𝕃 filepath
get-all-deps-h ts fm result store with new-deps (include-elt.deps $ get-include-elt ts fm) ([ fm ] ++ store ++ result)
get-all-deps-h ts fm result [] | [] = fm :: result
get-all-deps-h ts fm result [] | (d :: ds) =
  get-all-deps-h ts d (fm :: result) ds
get-all-deps-h ts fm result (s :: ss) | [] =
  get-all-deps-h ts s (fm :: result) ss
get-all-deps-h ts fm result (s :: ss) | deps =
  get-all-deps-h ts s (fm :: result) (ss ++ deps)

get-all-deps : toplevel-state → filepath → 𝕃 filepath
get-all-deps ts fm = get-all-deps-h ts fm [] []

write-html : include-elt → (fm to : filepath) → IO ⊤
write-html ie fm to =
  let out = (λ fp → to ^ "/" ^ (takeFileName fp) ^ ".html")
      deps-tries = trie-mappings $ include-elt.import-to-dep ie
      imports = map (json-string ∘ fst) deps-tries
      paths = map (json-string ∘ (out ∘ snd)) deps-tries
      json-output = json-array (json-object ["source" , (json-string $ include-elt.source ie)]
                             :: include-elt-spans-to-json ie -- spans
                             :: json-object ["deps" , (json-array $ [ json-array imports ] ++ [ json-array paths ])]
                             :: [])
  in
  (readFiniteFile "cedille-template.html")>>=
  (λ html →
    let content = [[ html ]]
                  ⊹⊹ [[ "<script type=\"application/json\" id=\"spans\">" ]]
                  ⊹⊹ json-to-rope json-output
                  ⊹⊹ [[ "</script></html>" ]]
    in
    writeRopeToFile (out fm) content)

write-html-all : toplevel-state → (fm to : filepath) → IO ⊤ -- test function
write-html-all ts fm to =
  let ie = get-include-elt ts fm -- include-elt FOR one file
  in
-- What is a suitable path for html template?
--  (makeAbsolute fm) >>= (λ s → (putStrLn s))
--  putStrLn (makeAbsolute to) >>
--  t-write-html-all ts fm to >>
  putStrLn("writing html...") >>
  foldr'
    (createDirectoryIfMissing ff to)
    (λ fp io →
      let ie = get-include-elt ts fp -- change to get-...-if?
          -- out = to ^ "/" ^ (takeFileName fp) ^ ".html" -- issue may happen when dir ends with "/"...
      in
      io >> (write-html ie fp to))
    (get-all-deps ts fm)
