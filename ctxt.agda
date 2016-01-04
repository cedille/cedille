module ctxt where

open import lib
open import cedille-types

data ctxt-info : Set where

  -- for declaring a variable to have a given type (with no definition)
  term-decl : type → ctxt-info

  -- for defining a variable to equal a term with a given type
  term-def : term → type → ctxt-info

  -- for declaring a variable to have a given kind (with no definition)
  type-decl : kind → ctxt-info

  -- for defining a variable to equal a type with a given kind
  type-def : type → kind → ctxt-info

  -- for defining a variable to equal a kind
  kind-def : kind → ctxt-info

  -- for a recursive type definition
  rec-def : type → kind → ctxt-info

data ctxt : Set where
  mk-ctxt : trie ctxt-info → ctxt

new-ctxt : ctxt
new-ctxt = mk-ctxt empty-trie

ctxt-term-decl : var → type → ctxt → ctxt
ctxt-term-decl v t (mk-ctxt i) = mk-ctxt (trie-insert i v (term-decl t))

ctxt-type-decl : var → kind → ctxt → ctxt
ctxt-type-decl v k (mk-ctxt i) = mk-ctxt (trie-insert i v (type-decl k))

ctxt-type-def : var → type → kind → ctxt → ctxt
ctxt-type-def v t k (mk-ctxt i) = mk-ctxt (trie-insert i v (type-def t k))

ctxt-term-def : var → term → type → ctxt → ctxt
ctxt-term-def v t tp (mk-ctxt i) = mk-ctxt (trie-insert i v (term-def t tp))

ctxt-tk-decl : var → tk → ctxt → ctxt
ctxt-tk-decl x (Tkt t) Γ = ctxt-term-decl x t Γ 
ctxt-tk-decl x (Tkk k) Γ = ctxt-type-decl x k Γ 

ctxt-rec-def : var → type → kind → ctxt → ctxt
ctxt-rec-def v t k (mk-ctxt i) = mk-ctxt (trie-insert i v (rec-def t k))

----------------------------------------------------------------------
-- lookup functions
----------------------------------------------------------------------

-- look for a kind for the given var, which is assumed to be a type
ctxt-lookup-type-var : ctxt → var → maybe kind
ctxt-lookup-type-var (mk-ctxt i) v with trie-lookup i v
ctxt-lookup-type-var (mk-ctxt i) v | just (type-decl k) = just k
ctxt-lookup-type-var (mk-ctxt i) v | just (type-def _ k) = just k
ctxt-lookup-type-var (mk-ctxt i) v | just (rec-def _ k) = just k
ctxt-lookup-type-var (mk-ctxt i) v | _ = nothing

ctxt-lookup-term-var : ctxt → var → maybe type
ctxt-lookup-term-var (mk-ctxt i) v with trie-lookup i v
ctxt-lookup-term-var (mk-ctxt i) v | just (term-decl t) = just t
ctxt-lookup-term-var (mk-ctxt i) v | just (term-def _ t) = just t
ctxt-lookup-term-var (mk-ctxt i) v | _ = nothing

ctxt-lookup-kind-var : ctxt → var → 𝔹
ctxt-lookup-kind-var (mk-ctxt i) v with trie-lookup i v
ctxt-lookup-kind-var (mk-ctxt i) v | just (kind-def _) = tt
ctxt-lookup-kind-var (mk-ctxt i) v | _ = ff

ctxt-lookup-term-var-def : ctxt → var → maybe term
ctxt-lookup-term-var-def (mk-ctxt i) v with trie-lookup i v
ctxt-lookup-term-var-def (mk-ctxt i) v | just (term-def t _) = just t
ctxt-lookup-term-var-def (mk-ctxt i) v | _ = nothing

ctxt-lookup-type-var-def : ctxt → var → maybe type
ctxt-lookup-type-var-def (mk-ctxt i) v with trie-lookup i v
ctxt-lookup-type-var-def (mk-ctxt i) v | just (type-def t _) = just t
ctxt-lookup-type-var-def (mk-ctxt i) v | _ = nothing

ctxt-lookup-kind-var-def : ctxt → var → maybe kind
ctxt-lookup-kind-var-def (mk-ctxt i) x with trie-lookup i x
ctxt-lookup-kind-var-def (mk-ctxt i) x | just (kind-def k) = just k
ctxt-lookup-kind-var-def (mk-ctxt i) x | _ = nothing

ctxt-binds-var : ctxt → var → 𝔹
ctxt-binds-var (mk-ctxt i) x = trie-contains i x
