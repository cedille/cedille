module ctxt where

open import lib
open import cedille-types
open import syntax-util
open import to-string

{- we will generally keep classifiers of variables in hnf in the ctxt, although
   we will not necessarily unfold recursive type definitions. -}

data ctxt-info : Set where

  -- for declaring a variable to have a given type (with no definition)
  term-decl : type → ctxt-info

  -- for defining a variable to equal a term with a given type
  term-def : term → type → ctxt-info

  -- for untyped term definitions (used only when checking recursive datatype definitions)
  term-udef : term → ctxt-info

  -- for declaring a variable to have a given kind (with no definition)
  type-decl : kind → ctxt-info

  -- for defining a variable to equal a type with a given kind
  type-def : type → kind → ctxt-info

  -- for defining a variable to equal a type, without a kind
  type-udef : type → ctxt-info

  -- for defining a variable to equal a kind
  kind-def : kind → ctxt-info

  -- to rename a variable at any level to another
  rename-def : var → ctxt-info

  -- for a recursive type definition
  rec-def : type → kind → ctxt-info

  -- representing a declaration of a variable with no other information about it
  var-decl : ctxt-info

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

ctxt-kind-def : var → kind → ctxt → ctxt
ctxt-kind-def v k (mk-ctxt i) = mk-ctxt (trie-insert i v (kind-def k))

ctxt-type-udef : var → type → ctxt → ctxt
ctxt-type-udef v t (mk-ctxt i) = mk-ctxt (trie-insert i v (type-udef t))

ctxt-term-def : var → term → type → ctxt → ctxt
ctxt-term-def v t tp (mk-ctxt i) = mk-ctxt (trie-insert i v (term-def t tp))

ctxt-term-udef : var → term → ctxt → ctxt
ctxt-term-udef v t (mk-ctxt i) = mk-ctxt (trie-insert i v (term-udef t))

ctxt-var-decl : var → ctxt → ctxt
ctxt-var-decl v (mk-ctxt i) = mk-ctxt (trie-insert i v var-decl)

ctxt-rename-rep : ctxt → var → var
ctxt-rename-rep (mk-ctxt i) v with trie-lookup i v 
ctxt-rename-rep (mk-ctxt i) v | just (rename-def v') = v'
ctxt-rename-rep (mk-ctxt i) v | _ = v

ctxt-eq-rep : ctxt → var → var → 𝔹
ctxt-eq-rep Γ x y = (ctxt-rename-rep Γ x) =string (ctxt-rename-rep Γ y)

{- add a renaming mapping the first variable to the second, unless they are equal.
   Notice that adding a renaming for v will overwrite any other declarations for v. -}
ctxt-rename : var → var → ctxt → ctxt
ctxt-rename v v' (mk-ctxt i) = if (v =string v') then (mk-ctxt i) else (mk-ctxt (trie-insert i v (rename-def v')))

ctxt-tk-decl : var → tk → ctxt → ctxt
ctxt-tk-decl x (Tkt t) Γ = ctxt-term-decl x t Γ 
ctxt-tk-decl x (Tkk k) Γ = ctxt-type-decl x k Γ 

ctxt-tk-def : var → var → tk → ctxt → ctxt
ctxt-tk-def x y (Tkt t) Γ = ctxt-term-def x (Var posinfo-gen y) t Γ 
ctxt-tk-def x y (Tkk k) Γ = ctxt-type-def x (TpVar posinfo-gen y) k Γ 

ctxt-rec-def : var → type → kind → ctxt → ctxt
ctxt-rec-def v t k (mk-ctxt i) = mk-ctxt (trie-insert i v (rec-def t k))

ctxt-binding-to-string : string × ctxt-info → string
ctxt-binding-to-string (x , term-decl tp) = "term " ^ x ^ " : " ^ type-to-string tp 
ctxt-binding-to-string (x , term-def t tp) = "term " ^ x ^ " = " ^ term-to-string t ^ " : " ^ type-to-string tp 
ctxt-binding-to-string (x , term-udef t) = "term " ^ x ^ " = " ^ term-to-string t 
ctxt-binding-to-string (x , type-decl k) = "type " ^ x ^ " : " ^ kind-to-string k 
ctxt-binding-to-string (x , type-def tp k) = "type " ^ x ^ " = " ^ type-to-string tp ^ " : " ^ kind-to-string k 
ctxt-binding-to-string (x , type-udef tp) = "type " ^ x ^ " = " ^ type-to-string tp
ctxt-binding-to-string (x , kind-def k) = "type " ^ x ^ " = " ^ kind-to-string k 
ctxt-binding-to-string (x , rename-def y) = "rename " ^ x ^ " to " ^ y 
ctxt-binding-to-string (x , rec-def tp k) = "rec " ^ x ^ " = " ^ type-to-string tp ^ " : " ^ kind-to-string k 
ctxt-binding-to-string (x , var-decl) = "expr " ^ x

ctxt-to-string : ctxt → string
ctxt-to-string (mk-ctxt i) = "[" ^ (string-concat-sep-map " | " ctxt-binding-to-string (trie-mappings i)) ^ "]"

local-ctxt-to-string : ctxt → string
local-ctxt-to-string (mk-ctxt i) = "[" ^ (string-concat-sep-map " | " ctxt-binding-to-string (filter helper (trie-mappings i))) ^ "]"
  where helper : string × ctxt-info → 𝔹
        helper (_ , term-decl _) = tt
        helper (_ , type-decl _) = tt
        helper _ = ff

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
ctxt-lookup-term-var-def (mk-ctxt i) v | just (term-udef t) = just t
ctxt-lookup-term-var-def (mk-ctxt i) v | _ = nothing

ctxt-lookup-type-var-def : ctxt → var → maybe type
ctxt-lookup-type-var-def (mk-ctxt i) v with trie-lookup i v
ctxt-lookup-type-var-def (mk-ctxt i) v | just (type-def t _) = just t
ctxt-lookup-type-var-def (mk-ctxt i) v | just (type-udef t) = just t
ctxt-lookup-type-var-def (mk-ctxt i) v | _ = nothing

ctxt-lookup-type-var-rec-def : ctxt → var → maybe type
ctxt-lookup-type-var-rec-def (mk-ctxt i) v with trie-lookup i v
ctxt-lookup-type-var-rec-def (mk-ctxt i) v | just (rec-def t _) = just t
ctxt-lookup-type-var-rec-def (mk-ctxt i) v | _ = nothing

ctxt-lookup-kind-var-def : ctxt → var → maybe kind
ctxt-lookup-kind-var-def (mk-ctxt i) x with trie-lookup i x
ctxt-lookup-kind-var-def (mk-ctxt i) x | just (kind-def k) = just k
ctxt-lookup-kind-var-def (mk-ctxt i) x | _ = nothing

ctxt-binds-var : ctxt → var → 𝔹
ctxt-binds-var (mk-ctxt i) x = trie-contains i x
