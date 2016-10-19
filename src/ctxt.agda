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

  -- for untyped term definitions 
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

sym-info : Set
sym-info = ctxt-info × location

data ctxt : Set where
  mk-ctxt : (filename : string) →
            (syms : trie (𝕃 string)) → -- map each filename to the symbols declared in that file
            (i : trie sym-info) → -- map symbols (from Cedille files) to their ctxt-info and location
            ctxt

new-ctxt : (filename : string) → ctxt
new-ctxt filename = mk-ctxt filename empty-trie empty-trie

ctxt-get-info : var → ctxt → maybe sym-info
ctxt-get-info v (mk-ctxt _ _ i) = trie-lookup i v

ctxt-restore-info : ctxt → string → maybe sym-info → ctxt
ctxt-restore-info (mk-ctxt f syms i) x nothing = mk-ctxt f syms (trie-remove i x)
ctxt-restore-info (mk-ctxt f syms i) x (just n) = mk-ctxt f syms (trie-insert i x n)

ctxt-term-decl : posinfo → var → type → ctxt → ctxt
ctxt-term-decl p v t (mk-ctxt filename syms i) = mk-ctxt filename 
                                                    (trie-insert-append syms filename v)
                                                    (trie-insert i v (term-decl t , (filename , p)))

ctxt-type-decl : posinfo → var → kind → ctxt → ctxt
ctxt-type-decl p v k (mk-ctxt filename syms i) = mk-ctxt filename 
                                                    (trie-insert-append syms filename v)
                                                    (trie-insert i v (type-decl k , (filename , p)))

ctxt-type-def : posinfo → var → type → kind → ctxt → ctxt
ctxt-type-def p v t k (mk-ctxt filename syms i) = mk-ctxt filename 
                                                    (trie-insert-append syms filename v)
                                                    (trie-insert i v (type-def t k , (filename , p)))

ctxt-kind-def : posinfo → var → kind → ctxt → ctxt
ctxt-kind-def p v k (mk-ctxt filename syms i) = mk-ctxt filename 
                                                    (trie-insert-append syms filename v)
                                                    (trie-insert i v (kind-def k , (filename , p)))

ctxt-type-udef : posinfo → var → type → ctxt → ctxt
ctxt-type-udef p v t (mk-ctxt filename syms i) = mk-ctxt filename 
                                                    (trie-insert-append syms filename v)
                                                    (trie-insert i v (type-udef t , (filename , p)))

ctxt-term-def : posinfo → var → term → type → ctxt → ctxt
ctxt-term-def p v t tp (mk-ctxt filename syms i) = mk-ctxt filename 
                                                    (trie-insert-append syms filename v)
                                                    (trie-insert i v (term-def t tp , (filename , p)))

ctxt-term-udef : posinfo → var → term → ctxt → ctxt
ctxt-term-udef p v t (mk-ctxt filename syms i) = mk-ctxt filename 
                                                    (trie-insert-append syms filename v)
                                                    (trie-insert i v (term-udef t , (filename , p)))

ctxt-var-decl : posinfo → var → ctxt → ctxt
ctxt-var-decl p v (mk-ctxt filename syms i) = mk-ctxt filename 
                                                    (trie-insert-append syms filename v)
                                                    (trie-insert i v (var-decl , (filename , p)))

ctxt-var-decl-if : posinfo → var → ctxt → ctxt
ctxt-var-decl-if p v Γ with Γ
ctxt-var-decl-if p v Γ | mk-ctxt filename syms i with trie-lookup i v
ctxt-var-decl-if p v Γ | mk-ctxt filename syms i | just (rename-def _ , _) = Γ
ctxt-var-decl-if p v Γ | mk-ctxt filename syms i | just (var-decl , _) = Γ
ctxt-var-decl-if p v Γ | mk-ctxt filename syms i | _ = 
  mk-ctxt filename (trie-insert-append syms filename v)
     (trie-insert i v (var-decl , (filename , p)))

ctxt-rename-rep : ctxt → var → var
ctxt-rename-rep (mk-ctxt filename syms i) v with trie-lookup i v 
ctxt-rename-rep (mk-ctxt filename syms i) v | just (rename-def v' , _) = v'
ctxt-rename-rep (mk-ctxt filename syms i) v | _ = v

-- we assume that only the left variable might have been renamed
ctxt-eq-rep : ctxt → var → var → 𝔹
ctxt-eq-rep Γ x y = (ctxt-rename-rep Γ x) =string y

{- add a renaming mapping the first variable to the second, unless they are equal.
   Notice that adding a renaming for v will overwrite any other declarations for v. -}
ctxt-rename : posinfo → var → var → ctxt → ctxt
ctxt-rename p v v' (mk-ctxt filename syms i) = 
  (mk-ctxt filename (trie-insert-append syms filename v)
      (trie-insert i v (rename-def v' , (filename , p))))

ctxt-tk-decl : posinfo → var → tk → ctxt → ctxt
ctxt-tk-decl p x (Tkt t) Γ = ctxt-term-decl p x t Γ 
ctxt-tk-decl p x (Tkk k) Γ = ctxt-type-decl p x k Γ 

ctxt-tk-def : posinfo → var → var → tk → ctxt → ctxt
ctxt-tk-def p x y (Tkt t) Γ = ctxt-term-def p x (Var posinfo-gen y) t Γ 
ctxt-tk-def p x y (Tkk k) Γ = ctxt-type-def p x (TpVar posinfo-gen y) k Γ 

ctxt-rec-def : posinfo → var → type → kind → ctxt → ctxt
ctxt-rec-def p v t k (mk-ctxt filename syms i) = 
  mk-ctxt filename (trie-insert-append syms filename v)
          (trie-insert i v (rec-def t k , (filename , p)))

----------------------------------------------------------------------
-- lookup functions
----------------------------------------------------------------------

-- look for a kind for the given var, which is assumed to be a type
ctxt-lookup-type-var : ctxt → var → maybe kind
ctxt-lookup-type-var (mk-ctxt _ _ i) v with trie-lookup i v
ctxt-lookup-type-var (mk-ctxt _ _ i) v | just (type-decl k , _) = just k
ctxt-lookup-type-var (mk-ctxt _ _ i) v | just (type-def _ k , _) = just k
ctxt-lookup-type-var (mk-ctxt _ _ i) v | just (rec-def _ k , _) = just k
ctxt-lookup-type-var (mk-ctxt _ _ i) v | _ = nothing

ctxt-lookup-term-var : ctxt → var → maybe type
ctxt-lookup-term-var (mk-ctxt _ _ i) v with trie-lookup i v
ctxt-lookup-term-var (mk-ctxt _ _ i) v | just (term-decl t , _) = just t
ctxt-lookup-term-var (mk-ctxt _ _ i) v | just (term-def _ t , _) = just t
ctxt-lookup-term-var (mk-ctxt _ _ i) v | _ = nothing

ctxt-lookup-var-tk : ctxt → var → maybe tk
ctxt-lookup-var-tk (mk-ctxt _ _ i) v with trie-lookup i v
ctxt-lookup-var-tk (mk-ctxt _ _ i) v | just (type-decl k , _) = just (Tkk k)
ctxt-lookup-var-tk (mk-ctxt _ _ i) v | just (type-def _ k , _) = just (Tkk k)
ctxt-lookup-var-tk (mk-ctxt _ _ i) v | just (term-decl t , _) = just (Tkt t)
ctxt-lookup-var-tk (mk-ctxt _ _ i) v | just (term-def _ t , _) = just (Tkt t)
ctxt-lookup-var-tk (mk-ctxt _ _ i) v | _ = nothing

ctxt-lookup-kind-var : ctxt → var → 𝔹
ctxt-lookup-kind-var (mk-ctxt _ _ i) v with trie-lookup i v
ctxt-lookup-kind-var (mk-ctxt _ _ i) v | just (kind-def _ , _) = tt
ctxt-lookup-kind-var (mk-ctxt _ _ i) v | _ = ff

ctxt-lookup-term-var-def : ctxt → var → maybe term
ctxt-lookup-term-var-def (mk-ctxt _ _ i) v with trie-lookup i v
ctxt-lookup-term-var-def (mk-ctxt _ _ i) v | just (term-def t _ , _) = just t
ctxt-lookup-term-var-def (mk-ctxt _ _ i) v | just (term-udef t , _) = just t
ctxt-lookup-term-var-def (mk-ctxt _ _ i) v | _ = nothing

ctxt-lookup-type-var-def : ctxt → var → maybe type
ctxt-lookup-type-var-def (mk-ctxt _ _ i) v with trie-lookup i v
ctxt-lookup-type-var-def (mk-ctxt _ _ i) v | just (type-def t _ , _) = just t
ctxt-lookup-type-var-def (mk-ctxt _ _ i) v | just (type-udef t , _) = just t
ctxt-lookup-type-var-def (mk-ctxt _ _ i) v | _ = nothing

ctxt-lookup-type-var-rec-def : ctxt → var → maybe type
ctxt-lookup-type-var-rec-def (mk-ctxt _ _ i) v with trie-lookup i v
ctxt-lookup-type-var-rec-def (mk-ctxt _ _ i) v | just (rec-def t _ , _) = just t
ctxt-lookup-type-var-rec-def (mk-ctxt _ _ i) v | _ = nothing

ctxt-lookup-kind-var-def : ctxt → var → maybe kind
ctxt-lookup-kind-var-def (mk-ctxt _ _ i) x with trie-lookup i x
ctxt-lookup-kind-var-def (mk-ctxt _ _ i) x | just (kind-def k , _) = just k
ctxt-lookup-kind-var-def (mk-ctxt _ _ i) x | _ = nothing

ctxt-binds-var : ctxt → var → 𝔹
ctxt-binds-var (mk-ctxt _ _ i) x = trie-contains i x

ctxt-defines-var : ctxt → var → 𝔹
ctxt-defines-var (mk-ctxt _ _ i) x with trie-lookup i x
ctxt-defines-var (mk-ctxt _ _ i) x | just (term-def _ _ , _) = tt
ctxt-defines-var (mk-ctxt _ _ i) x | just (term-udef _ , _) = tt
ctxt-defines-var (mk-ctxt _ _ i) x | just (type-def _ _ , _) = tt
ctxt-defines-var (mk-ctxt _ _ i) x | just (type-udef _ , _) = tt
ctxt-defines-var (mk-ctxt _ _ i) x | just (kind-def _ , _) = tt
ctxt-defines-var (mk-ctxt _ _ i) x | just (rec-def _ _ , _) = tt
ctxt-defines-var (mk-ctxt _ _ i) x | _ = ff
----------------------------------------------------------------------

ctxt-var-location : ctxt → var → location
ctxt-var-location (mk-ctxt _ _ i) x with trie-lookup i x
ctxt-var-location (mk-ctxt _ _ i) x | just (_ , l) = l
ctxt-var-location (mk-ctxt _ _ i) x | nothing = "missing" , "missing"

ctxt-set-current-file : ctxt → (filename : string) → ctxt
ctxt-set-current-file (mk-ctxt _ syms i) filename = mk-ctxt filename syms i

ctxt-clear-symbol : ctxt → string → ctxt
ctxt-clear-symbol (mk-ctxt f syms i) x = mk-ctxt f (trie-remove syms x) (trie-remove i x)

ctxt-clear-symbols : ctxt → 𝕃 string → ctxt
ctxt-clear-symbols Γ [] = Γ
ctxt-clear-symbols Γ (v :: vs) = ctxt-clear-symbols (ctxt-clear-symbol Γ v) vs

ctxt-clear-symbols-of-file : ctxt → (filename : string) → ctxt
ctxt-clear-symbols-of-file (mk-ctxt f syms i) filename = mk-ctxt f (trie-insert syms filename [])
                                                              (hremove i (trie-lookup𝕃 syms filename))
  where hremove : ∀ {A : Set} → trie A → 𝕃 string → trie A
        hremove i [] = i
        hremove i (x :: xs) = hremove (trie-remove i x) xs

ctxt-initiate-file : ctxt → (filename : string) → ctxt
ctxt-initiate-file Γ filename = ctxt-set-current-file (ctxt-clear-symbols-of-file Γ filename) filename

ctxt-get-current-filename : ctxt → string
ctxt-get-current-filename (mk-ctxt filename _ _) = filename


