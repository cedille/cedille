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

data ctxt-t : Set where
  ctxt : trie ctxt-info → ctxt-t

new-ctxt : ctxt-t
new-ctxt = ctxt empty-trie
