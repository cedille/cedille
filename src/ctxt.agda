module ctxt where

open import lib
open import cedille-types
open import syntax-util
open import to-string

location : Set
location = string × posinfo -- file path and starting position in the file 

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
  mk-ctxt : (current-file : string) → trie (ctxt-info × location) → ctxt

new-ctxt : (current-file : string) → ctxt
new-ctxt file-name = mk-ctxt file-name empty-trie

ctxt-term-decl : posinfo → var → type → ctxt → ctxt
ctxt-term-decl p v t (mk-ctxt cur-file i) = mk-ctxt cur-file (trie-insert i v (term-decl t , (cur-file , p)))

ctxt-type-decl : posinfo → var → kind → ctxt → ctxt
ctxt-type-decl p v k (mk-ctxt cur-file i) = mk-ctxt cur-file (trie-insert i v (type-decl k , (cur-file , p)))

ctxt-type-def : posinfo → var → type → kind → ctxt → ctxt
ctxt-type-def p v t k (mk-ctxt cur-file i) = mk-ctxt cur-file (trie-insert i v (type-def t k , (cur-file , p)))

ctxt-kind-def : posinfo → var → kind → ctxt → ctxt
ctxt-kind-def p v k (mk-ctxt cur-file i) = mk-ctxt cur-file (trie-insert i v (kind-def k , (cur-file , p)))

ctxt-type-udef : posinfo → var → type → ctxt → ctxt
ctxt-type-udef p v t (mk-ctxt cur-file i) = mk-ctxt cur-file (trie-insert i v (type-udef t , (cur-file , p)))

ctxt-term-def : posinfo → var → term → type → ctxt → ctxt
ctxt-term-def p v t tp (mk-ctxt cur-file i) = mk-ctxt cur-file (trie-insert i v (term-def t tp , (cur-file , p)))

ctxt-term-udef : posinfo → var → term → ctxt → ctxt
ctxt-term-udef p v t (mk-ctxt cur-file i) = mk-ctxt cur-file (trie-insert i v (term-udef t , (cur-file , p)))

ctxt-var-decl : posinfo → var → ctxt → ctxt
ctxt-var-decl p v (mk-ctxt cur-file i) = mk-ctxt cur-file (trie-insert i v (var-decl , (cur-file , p)))

ctxt-var-decl-if : posinfo → var → ctxt → ctxt
ctxt-var-decl-if p v (mk-ctxt cur-file i) = 
  if trie-contains i v then (mk-ctxt cur-file i) else (mk-ctxt cur-file (trie-insert i v (var-decl , (cur-file , p))))

ctxt-rename-rep : ctxt → var → var
ctxt-rename-rep (mk-ctxt cur-file i) v with trie-lookup i v 
ctxt-rename-rep (mk-ctxt cur-file i) v | just (rename-def v' , _) = v'
ctxt-rename-rep (mk-ctxt cur-file i) v | _ = v

-- we assume that only the left variable might have been renamed
ctxt-eq-rep : ctxt → var → var → 𝔹
ctxt-eq-rep Γ x y = (ctxt-rename-rep Γ x) =string y

{- add a renaming mapping the first variable to the second, unless they are equal.
   Notice that adding a renaming for v will overwrite any other declarations for v. -}
ctxt-rename : posinfo → var → var → ctxt → ctxt
ctxt-rename p v v' (mk-ctxt cur-file i) = (mk-ctxt cur-file (trie-insert i v (rename-def v' , (cur-file , p))))

ctxt-tk-decl : posinfo → var → tk → ctxt → ctxt
ctxt-tk-decl p x (Tkt t) Γ = ctxt-term-decl p x t Γ 
ctxt-tk-decl p x (Tkk k) Γ = ctxt-type-decl p x k Γ 

ctxt-tk-def : posinfo → var → var → tk → ctxt → ctxt
ctxt-tk-def p x y (Tkt t) Γ = ctxt-term-def p x (Var posinfo-gen y) t Γ 
ctxt-tk-def p x y (Tkk k) Γ = ctxt-type-def p x (TpVar posinfo-gen y) k Γ 

ctxt-rec-def : posinfo → var → type → kind → ctxt → ctxt
ctxt-rec-def p v t k (mk-ctxt cur-file i) = mk-ctxt cur-file (trie-insert i v (rec-def t k , (cur-file , p)))

ctxt-binding-to-string : string × (ctxt-info × location) → string
ctxt-binding-to-string (x , term-decl tp , _) = "term " ^ x ^ " : " ^ type-to-string tp 
ctxt-binding-to-string (x , term-def t tp , _) = "term " ^ x ^ " = " ^ term-to-string t ^ " : " ^ type-to-string tp 
ctxt-binding-to-string (x , term-udef t , _) = "term " ^ x ^ " = " ^ term-to-string t 
ctxt-binding-to-string (x , type-decl k , _) = "type " ^ x ^ " : " ^ kind-to-string k 
ctxt-binding-to-string (x , type-def tp k , _) = "type " ^ x ^ " = " ^ type-to-string tp ^ " : " ^ kind-to-string k 
ctxt-binding-to-string (x , type-udef tp , _) = "type " ^ x ^ " = " ^ type-to-string tp
ctxt-binding-to-string (x , kind-def k , _) = "type " ^ x ^ " = " ^ kind-to-string k 
ctxt-binding-to-string (x , rename-def y , _) = "rename " ^ x ^ " to " ^ y 
ctxt-binding-to-string (x , rec-def tp k , _) = "rec " ^ x ^ " = " ^ type-to-string tp ^ " : " ^ kind-to-string k 
ctxt-binding-to-string (x , var-decl , _) = "expr " ^ x

ctxt-to-string : ctxt → string
ctxt-to-string (mk-ctxt cur-file i) = "[" ^ (string-concat-sep-map " | " ctxt-binding-to-string (trie-mappings i)) ^ "]"

local-ctxt-to-string : ctxt → string
local-ctxt-to-string (mk-ctxt cur-file i) = "[" ^ (string-concat-sep-map " | " ctxt-binding-to-string (filter helper (trie-mappings i))) ^ "]"
  where helper : string × ctxt-info × location → 𝔹
        helper (_ , term-decl _ , _) = tt
        helper (_ , type-decl _ , _) = tt
        helper _ = ff

----------------------------------------------------------------------
-- lookup functions
----------------------------------------------------------------------

-- look for a kind for the given var, which is assumed to be a type
ctxt-lookup-type-var : ctxt → var → maybe kind
ctxt-lookup-type-var (mk-ctxt _ i) v with trie-lookup i v
ctxt-lookup-type-var (mk-ctxt _ i) v | just (type-decl k , _) = just k
ctxt-lookup-type-var (mk-ctxt _ i) v | just (type-def _ k , _) = just k
ctxt-lookup-type-var (mk-ctxt _ i) v | just (rec-def _ k , _) = just k
ctxt-lookup-type-var (mk-ctxt _ i) v | _ = nothing

ctxt-lookup-term-var : ctxt → var → maybe type
ctxt-lookup-term-var (mk-ctxt _ i) v with trie-lookup i v
ctxt-lookup-term-var (mk-ctxt _ i) v | just (term-decl t , _) = just t
ctxt-lookup-term-var (mk-ctxt _ i) v | just (term-def _ t , _) = just t
ctxt-lookup-term-var (mk-ctxt _ i) v | _ = nothing

ctxt-lookup-var-tk : ctxt → var → maybe tk
ctxt-lookup-var-tk (mk-ctxt _ i) v with trie-lookup i v
ctxt-lookup-var-tk (mk-ctxt _ i) v | just (type-decl k , _) = just (Tkk k)
ctxt-lookup-var-tk (mk-ctxt _ i) v | just (type-def _ k , _) = just (Tkk k)
ctxt-lookup-var-tk (mk-ctxt _ i) v | just (term-decl t , _) = just (Tkt t)
ctxt-lookup-var-tk (mk-ctxt _ i) v | just (term-def _ t , _) = just (Tkt t)
ctxt-lookup-var-tk (mk-ctxt _ i) v | _ = nothing

ctxt-lookup-kind-var : ctxt → var → 𝔹
ctxt-lookup-kind-var (mk-ctxt _ i) v with trie-lookup i v
ctxt-lookup-kind-var (mk-ctxt _ i) v | just (kind-def _ , _) = tt
ctxt-lookup-kind-var (mk-ctxt _ i) v | _ = ff

ctxt-lookup-term-var-def : ctxt → var → maybe term
ctxt-lookup-term-var-def (mk-ctxt _ i) v with trie-lookup i v
ctxt-lookup-term-var-def (mk-ctxt _ i) v | just (term-def t _ , _) = just t
ctxt-lookup-term-var-def (mk-ctxt _ i) v | just (term-udef t , _) = just t
ctxt-lookup-term-var-def (mk-ctxt _ i) v | _ = nothing

ctxt-lookup-type-var-def : ctxt → var → maybe type
ctxt-lookup-type-var-def (mk-ctxt _ i) v with trie-lookup i v
ctxt-lookup-type-var-def (mk-ctxt _ i) v | just (type-def t _ , _) = just t
ctxt-lookup-type-var-def (mk-ctxt _ i) v | just (type-udef t , _) = just t
ctxt-lookup-type-var-def (mk-ctxt _ i) v | _ = nothing

ctxt-lookup-type-var-rec-def : ctxt → var → maybe type
ctxt-lookup-type-var-rec-def (mk-ctxt _ i) v with trie-lookup i v
ctxt-lookup-type-var-rec-def (mk-ctxt _ i) v | just (rec-def t _ , _) = just t
ctxt-lookup-type-var-rec-def (mk-ctxt _ i) v | _ = nothing

ctxt-lookup-kind-var-def : ctxt → var → maybe kind
ctxt-lookup-kind-var-def (mk-ctxt _ i) x with trie-lookup i x
ctxt-lookup-kind-var-def (mk-ctxt _ i) x | just (kind-def k , _) = just k
ctxt-lookup-kind-var-def (mk-ctxt _ i) x | _ = nothing

ctxt-binds-var : ctxt → var → 𝔹
ctxt-binds-var (mk-ctxt _ i) x = trie-contains i x

ctxt-var-location : ctxt → var → location
ctxt-var-location (mk-ctxt _ i) x with trie-lookup i x
ctxt-var-location (mk-ctxt _ i) x | just (_ , l) = l
ctxt-var-location (mk-ctxt _ i) x | nothing = "missing" , "missing"

ctxt-set-current-file : ctxt → string → ctxt
ctxt-set-current-file (mk-ctxt _ i) file-name = mk-ctxt file-name i

ctxt-get-current-file : ctxt → string
ctxt-get-current-file (mk-ctxt filename i) = filename
