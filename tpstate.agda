module tpstate where

open import lib
open import cedille-types

data tpstate : Set where
  mk-tpstate : string → -- output for the user

               trie term → -- untyped term definitions

               trie (term × type) → -- typed term definitions

               trie (type × kind) → -- kinded type definitions

               trie kind → -- kind definitions

               tpstate

add-typed-term-def : var → term → type → tpstate → tpstate
add-typed-term-def v trm tp (mk-tpstate o d td yd kd) = (mk-tpstate o d (trie-insert td v (trm , tp)) yd kd)

add-kinded-type-def : var → type → kind → tpstate → tpstate
add-kinded-type-def v tp knd (mk-tpstate o d td yd kd) = (mk-tpstate o d td (trie-insert yd v (tp , knd)) kd)

add-kind-def : var → kind → tpstate → tpstate
add-kind-def v knd (mk-tpstate o d td yd kd) = (mk-tpstate o d td yd (trie-insert kd v knd))

add-msg : string → tpstate → tpstate
add-msg m (mk-tpstate o d td yd kd) = mk-tpstate (o ^ m) d td yd kd

-- is the given string in the domain of any of the mappings in the typestate
in-dom-tpstate : tpstate → string → 𝔹
in-dom-tpstate (mk-tpstate _ d td yd kd) v = trie-contains d v || trie-contains td v || trie-contains yd v || trie-contains kd v

lookup-kind-var : tpstate → var → maybe kind
lookup-kind-var (mk-tpstate _ _ _ _ kd) v = trie-lookup kd v