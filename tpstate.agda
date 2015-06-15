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

