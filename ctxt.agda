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

  -- for a recursive type definition
  rec-def : type → kind → ctxt-info

data ctxt : Set where
  mk-ctxt : trie ctxt-info → ctxt

new-ctxt : ctxt
new-ctxt = mk-ctxt empty-trie

ctxt-term-decl : ctxt → var → type → ctxt
ctxt-term-decl (mk-ctxt i) v t = mk-ctxt (trie-insert i v (term-decl t))

ctxt-type-decl : ctxt → var → kind → ctxt
ctxt-type-decl (mk-ctxt i) v k = mk-ctxt (trie-insert i v (type-decl k))

ctxt-type-def : ctxt → var → type → kind → ctxt
ctxt-type-def (mk-ctxt i) v t k = mk-ctxt (trie-insert i v (type-def t k))

ctxt-term-def : ctxt → var → term → type → ctxt
ctxt-term-def (mk-ctxt i) v t tp = mk-ctxt (trie-insert i v (term-def t tp))

ctxt-tk-decl : ctxt → var → tk → ctxt
ctxt-tk-decl Γ x (Tkt t) = ctxt-term-decl Γ x t
ctxt-tk-decl Γ x (Tkk k) = ctxt-type-decl Γ x k

ctxt-rec-def : ctxt → var → type → kind → ctxt
ctxt-rec-def (mk-ctxt i) v t k = mk-ctxt (trie-insert i v (rec-def t k))

ctxt-lookup-kind : ctxt → var → maybe kind
ctxt-lookup-kind (mk-ctxt i) v with trie-lookup i v
ctxt-lookup-kind (mk-ctxt i) v | just (type-decl k) = just k
ctxt-lookup-kind (mk-ctxt i) v | just (type-def _ k) = just k
ctxt-lookup-kind (mk-ctxt i) v | just (rec-def _ k) = just k
ctxt-lookup-kind (mk-ctxt i) v | _ = nothing

ctxt-kind-def : ctxt → var → maybe kind
ctxt-kind-def (mk-ctxt i) x with trie-lookup i x
ctxt-kind-def (mk-ctxt i) x | just (kind-def k) = just k
ctxt-kind-def (mk-ctxt i) x | _ = nothing
