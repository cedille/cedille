module ctxt where

open import lib
open import cedille-types
open import general-util
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
  mk-ctxt : (unit-name : string) → (filename : string) → trie (𝕃 string) → trie (ctxt-info × location) → ctxt

new-ctxt : (unit-name : string) → (filename : string) → ctxt
new-ctxt unit-name filename = mk-ctxt unit-name filename empty-trie empty-trie

ctxt-term-decl : posinfo → var → type → ctxt → ctxt
ctxt-term-decl p v t (mk-ctxt cur-unit filename syms i) = mk-ctxt cur-unit filename 
                                                    (trie-insert-append syms cur-unit v)
                                                    (trie-insert i v (term-decl t , (filename , p)))

ctxt-type-decl : posinfo → var → kind → ctxt → ctxt
ctxt-type-decl p v k (mk-ctxt cur-unit filename syms i) = mk-ctxt cur-unit filename 
                                                    (trie-insert-append syms cur-unit v)
                                                    (trie-insert i v (type-decl k , (filename , p)))

ctxt-type-def : posinfo → var → type → kind → ctxt → ctxt
ctxt-type-def p v t k (mk-ctxt cur-unit filename syms i) = mk-ctxt cur-unit filename 
                                                    (trie-insert-append syms cur-unit v)
                                                    (trie-insert i v (type-def t k , (filename , p)))

ctxt-kind-def : posinfo → var → kind → ctxt → ctxt
ctxt-kind-def p v k (mk-ctxt cur-unit filename syms i) = mk-ctxt cur-unit filename 
                                                    (trie-insert-append syms cur-unit v)
                                                    (trie-insert i v (kind-def k , (filename , p)))

ctxt-type-udef : posinfo → var → type → ctxt → ctxt
ctxt-type-udef p v t (mk-ctxt cur-unit filename syms i) = mk-ctxt cur-unit filename 
                                                    (trie-insert-append syms cur-unit v)
                                                    (trie-insert i v (type-udef t , (filename , p)))

ctxt-term-def : posinfo → var → term → type → ctxt → ctxt
ctxt-term-def p v t tp (mk-ctxt cur-unit filename syms i) = mk-ctxt cur-unit filename 
                                                    (trie-insert-append syms cur-unit v)
                                                    (trie-insert i v (term-def t tp , (filename , p)))

ctxt-term-udef : posinfo → var → term → ctxt → ctxt
ctxt-term-udef p v t (mk-ctxt cur-unit filename syms i) = mk-ctxt cur-unit filename 
                                                    (trie-insert-append syms cur-unit v)
                                                    (trie-insert i v (term-udef t , (filename , p)))

ctxt-var-decl : posinfo → var → ctxt → ctxt
ctxt-var-decl p v (mk-ctxt cur-unit filename syms i) = mk-ctxt cur-unit filename 
                                                    (trie-insert-append syms cur-unit v)
                                                    (trie-insert i v (var-decl , (filename , p)))

ctxt-var-decl-if : posinfo → var → ctxt → ctxt
ctxt-var-decl-if p v (mk-ctxt cur-unit filename syms i) = 
  if trie-contains i v then (mk-ctxt cur-unit filename syms i) 
  else (mk-ctxt cur-unit filename (trie-insert-append syms cur-unit v)
            (trie-insert i v (var-decl , (filename , p))))

ctxt-rename-rep : ctxt → var → var
ctxt-rename-rep (mk-ctxt cur-unit filename syms i) v with trie-lookup i v 
ctxt-rename-rep (mk-ctxt cur-unit filename syms i) v | just (rename-def v' , _) = v'
ctxt-rename-rep (mk-ctxt cur-unit filename syms i) v | _ = v

-- we assume that only the left variable might have been renamed
ctxt-eq-rep : ctxt → var → var → 𝔹
ctxt-eq-rep Γ x y = (ctxt-rename-rep Γ x) =string y

{- add a renaming mapping the first variable to the second, unless they are equal.
   Notice that adding a renaming for v will overwrite any other declarations for v. -}
ctxt-rename : posinfo → var → var → ctxt → ctxt
ctxt-rename p v v' (mk-ctxt cur-unit filename syms i) = 
  (mk-ctxt cur-unit filename (trie-insert-append syms cur-unit v)
      (trie-insert i v (rename-def v' , (filename , p))))

ctxt-tk-decl : posinfo → var → tk → ctxt → ctxt
ctxt-tk-decl p x (Tkt t) Γ = ctxt-term-decl p x t Γ 
ctxt-tk-decl p x (Tkk k) Γ = ctxt-type-decl p x k Γ 

ctxt-tk-def : posinfo → var → var → tk → ctxt → ctxt
ctxt-tk-def p x y (Tkt t) Γ = ctxt-term-def p x (Var posinfo-gen y) t Γ 
ctxt-tk-def p x y (Tkk k) Γ = ctxt-type-def p x (TpVar posinfo-gen y) k Γ 

ctxt-rec-def : posinfo → var → type → kind → ctxt → ctxt
ctxt-rec-def p v t k (mk-ctxt cur-unit filename syms i) = 
  mk-ctxt cur-unit filename (trie-insert-append syms cur-unit v)
          (trie-insert i v (rec-def t k , (filename , p)))

----------------------------------------------------------------------
-- lookup functions
----------------------------------------------------------------------

-- look for a kind for the given var, which is assumed to be a type
ctxt-lookup-type-var : ctxt → var → maybe kind
ctxt-lookup-type-var (mk-ctxt _ _ _ i) v with trie-lookup i v
ctxt-lookup-type-var (mk-ctxt _ _ _ i) v | just (type-decl k , _) = just k
ctxt-lookup-type-var (mk-ctxt _ _ _ i) v | just (type-def _ k , _) = just k
ctxt-lookup-type-var (mk-ctxt _ _ _ i) v | just (rec-def _ k , _) = just k
ctxt-lookup-type-var (mk-ctxt _ _ _ i) v | _ = nothing

ctxt-lookup-term-var : ctxt → var → maybe type
ctxt-lookup-term-var (mk-ctxt _ _ _ i) v with trie-lookup i v
ctxt-lookup-term-var (mk-ctxt _ _ _ i) v | just (term-decl t , _) = just t
ctxt-lookup-term-var (mk-ctxt _ _ _ i) v | just (term-def _ t , _) = just t
ctxt-lookup-term-var (mk-ctxt _ _ _ i) v | _ = nothing

ctxt-lookup-var-tk : ctxt → var → maybe tk
ctxt-lookup-var-tk (mk-ctxt _ _ _ i) v with trie-lookup i v
ctxt-lookup-var-tk (mk-ctxt _ _ _ i) v | just (type-decl k , _) = just (Tkk k)
ctxt-lookup-var-tk (mk-ctxt _ _ _ i) v | just (type-def _ k , _) = just (Tkk k)
ctxt-lookup-var-tk (mk-ctxt _ _ _ i) v | just (term-decl t , _) = just (Tkt t)
ctxt-lookup-var-tk (mk-ctxt _ _ _ i) v | just (term-def _ t , _) = just (Tkt t)
ctxt-lookup-var-tk (mk-ctxt _ _ _ i) v | _ = nothing

ctxt-lookup-kind-var : ctxt → var → 𝔹
ctxt-lookup-kind-var (mk-ctxt _ _ _ i) v with trie-lookup i v
ctxt-lookup-kind-var (mk-ctxt _ _ _ i) v | just (kind-def _ , _) = tt
ctxt-lookup-kind-var (mk-ctxt _ _ _ i) v | _ = ff

ctxt-lookup-term-var-def : ctxt → var → maybe term
ctxt-lookup-term-var-def (mk-ctxt _ _ _ i) v with trie-lookup i v
ctxt-lookup-term-var-def (mk-ctxt _ _ _ i) v | just (term-def t _ , _) = just t
ctxt-lookup-term-var-def (mk-ctxt _ _ _ i) v | just (term-udef t , _) = just t
ctxt-lookup-term-var-def (mk-ctxt _ _ _ i) v | _ = nothing

ctxt-lookup-type-var-def : ctxt → var → maybe type
ctxt-lookup-type-var-def (mk-ctxt _ _ _ i) v with trie-lookup i v
ctxt-lookup-type-var-def (mk-ctxt _ _ _ i) v | just (type-def t _ , _) = just t
ctxt-lookup-type-var-def (mk-ctxt _ _ _ i) v | just (type-udef t , _) = just t
ctxt-lookup-type-var-def (mk-ctxt _ _ _ i) v | _ = nothing

ctxt-lookup-type-var-rec-def : ctxt → var → maybe type
ctxt-lookup-type-var-rec-def (mk-ctxt _ _ _ i) v with trie-lookup i v
ctxt-lookup-type-var-rec-def (mk-ctxt _ _ _ i) v | just (rec-def t _ , _) = just t
ctxt-lookup-type-var-rec-def (mk-ctxt _ _ _ i) v | _ = nothing

ctxt-lookup-kind-var-def : ctxt → var → maybe kind
ctxt-lookup-kind-var-def (mk-ctxt _ _ _ i) x with trie-lookup i x
ctxt-lookup-kind-var-def (mk-ctxt _ _ _ i) x | just (kind-def k , _) = just k
ctxt-lookup-kind-var-def (mk-ctxt _ _ _ i) x | _ = nothing

ctxt-binds-var : ctxt → var → 𝔹
ctxt-binds-var (mk-ctxt _ _ _ i) x = trie-contains i x

ctxt-var-location : ctxt → var → location
ctxt-var-location (mk-ctxt _ _ _ i) x with trie-lookup i x
ctxt-var-location (mk-ctxt _ _ _ i) x | just (_ , l) = l
ctxt-var-location (mk-ctxt _ _ _ i) x | nothing = "missing" , "missing"

ctxt-set-current-unit : ctxt → (unit-name : string) → (filename : string) → ctxt
ctxt-set-current-unit (mk-ctxt _ _ syms i) unit-name filename = mk-ctxt unit-name filename syms i

ctxt-clear-symbols-of-unit : ctxt → (unit-name : string) → ctxt
ctxt-clear-symbols-of-unit (mk-ctxt u f syms i) unit-name = mk-ctxt u f (trie-insert syms unit-name [])
                                                              (hremove i (trie-lookup𝕃 syms unit-name))
  where hremove : ∀ {A : Set} → trie A → 𝕃 string → trie A
        hremove i [] = i
        hremove i (x :: xs) = hremove (trie-remove i x) xs

ctxt-initiate-unit : ctxt → (unit-name : string) → (filename : string) → ctxt
ctxt-initiate-unit Γ unit-name filename = ctxt-set-current-unit (ctxt-clear-symbols-of-unit Γ unit-name) unit-name filename

ctxt-get-current-filename : ctxt → string
ctxt-get-current-filename (mk-ctxt _ filename _ _) = filename

ctxt-get-current-unit-name : ctxt → string
ctxt-get-current-unit-name (mk-ctxt unit-name _ _ _) = unit-name

