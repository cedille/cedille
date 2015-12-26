module ctxt where

open import lib
open import cedille-types

data ctxt-info : Set where

  -- for defining a variable to equal a term with a given type
  term-def : term → type → ctxt-info

  -- for defining a variable to equal a type with a given kind
  type-def : type → kind → ctxt-info

  -- for defining a variable to equal a kind
  kind-def : kind → ctxt-info

  -- for declaring a variable to have a given type (with no definition)
  term-decl : type → ctxt-info

  -- for declaring a variable to have a given kind (with no definition)
  type-decl : kind → ctxt-info

data ctxt : Set where
  mk-ctxt : trie ctxt-info → ctxt

new-ctxt : ctxt
new-ctxt = mk-ctxt empty-trie
