module ctxt where

open import lib
open import cedille-types
open import general-util
open import syntax-util

location : Set
location = string × posinfo -- file path and starting position in the file 

{- we will generally keep classifiers of variables in hnf in the ctxt, although
   we will not necessarily unfold recursive type definitions. -}

defScope : Set
defScope = 𝔹

localScope : defScope
localScope = tt

globalScope : defScope
globalScope = ff

defParams : Set
defParams = maybe params

data ctxt-info : Set where

  -- for declaring a variable to have a given type (with no definition)
  term-decl : type → ctxt-info

  -- for defining a variable to equal a term with a given type
  term-def : defParams → term → type → ctxt-info

  -- for untyped term definitions 
  term-udef : defParams → term → ctxt-info

  -- for declaring a variable to have a given kind (with no definition)
  type-decl : kind → ctxt-info

  -- for defining a variable to equal a type with a given kind
  type-def : defParams → type → kind → ctxt-info

  -- for defining a variable to equal a kind
  kind-def : params → params → kind → ctxt-info

  -- to rename a variable at any level to another
  rename-def : var → ctxt-info

  -- representing a declaration of a variable with no other information about it
  var-decl : ctxt-info

sym-info : Set
sym-info = ctxt-info × location

-- module filename, parameters, and qualifying substitution
mod-info : Set
mod-info = string × params × qualif

is-term-level : ctxt-info → 𝔹
is-term-level (term-decl _) = tt
is-term-level (term-def _ _ _) = tt
is-term-level (term-udef _ _) = tt
is-term-level _ = ff

data ctxt : Set where
  mk-ctxt : (mod : mod-info) →                     -- current module
            (syms : trie (𝕃 string)) →             -- map each filename to the symbols declared in that file
            (i : trie sym-info) →                  -- map symbols (from Cedille files) to their ctxt-info and location
            (sym-occurrences : trie (𝕃 (var × posinfo × string))) →  -- map symbols to a list of definitions they occur in (and relevant file info)
            ctxt

new-ctxt : (filename : string) → ctxt
new-ctxt filename = mk-ctxt (filename , ParamsNil , empty-trie) empty-trie empty-trie empty-trie

ctxt-get-info : var → ctxt → maybe sym-info
ctxt-get-info v (mk-ctxt _ _ i _) = trie-lookup i v

ctxt-restore-info : ctxt → string → maybe sym-info → ctxt
ctxt-restore-info (mk-ctxt f syms i symb-occs) x nothing = mk-ctxt f syms (trie-remove i x) symb-occs
ctxt-restore-info (mk-ctxt f syms i symb-occs) x (just n) = mk-ctxt f syms (trie-insert i x n) symb-occs

ctxt-restore-info* : ctxt → 𝕃 (string × maybe sym-info) → ctxt
ctxt-restore-info* Γ [] = Γ
ctxt-restore-info* Γ ((x , m) :: ms) = ctxt-restore-info* (ctxt-restore-info Γ x m) ms

ctxt-term-decl : posinfo → var → type → ctxt → ctxt
ctxt-term-decl p v t (mk-ctxt (filename , ps , q) syms i symb-occs) = mk-ctxt (filename , ps , q)
                                                    (trie-insert-append syms filename v)
                                                    (trie-insert i v (term-decl t , (filename , p)))
                                                    symb-occs

ctxt-type-decl : posinfo → var → kind → ctxt → ctxt
ctxt-type-decl p v k (mk-ctxt (filename , ps , q) syms i symb-occs) = mk-ctxt (filename , ps , q)
                                                    (trie-insert-append syms filename v)
                                                    (trie-insert i v (type-decl k , (filename , p)))
                                                    symb-occs

def-params : defScope → params → defParams
def-params tt ps = nothing
def-params ff ps = just ps

-- TODO roll "hnf Γ unfold-head t tt" into ctxt-*-def, after qualification
ctxt-type-def : posinfo → defScope → var → type → kind → ctxt → ctxt
ctxt-type-def p s v t k (mk-ctxt (filename , ps , q) syms i symb-occs) = mk-ctxt (filename , ps , qualif-insert-params q v ps)
                                                    (trie-insert-append syms filename v)
                                                    (trie-insert i v (type-def (def-params s ps) (qualif-type q t) (qualif-kind q k) , (filename , p)))
                                                    symb-occs

ctxt-kind-def : posinfo → var → params → kind → ctxt → ctxt
ctxt-kind-def p v ps2 k (mk-ctxt (filename , ps1 , q) syms i symb-occs) = mk-ctxt (filename , ps1 , qualif-insert-params q v ps1)
                                                    (trie-insert-append syms filename v)
                                                    (trie-insert i v (kind-def ps1 ps2 k , (filename , p)))
                                                    symb-occs

ctxt-term-def : posinfo → defScope → var → term → type → ctxt → ctxt
ctxt-term-def p s v t tp (mk-ctxt (filename , ps , q) syms i symb-occs) = mk-ctxt (filename , ps , qualif-insert-params q v ps)
                                                    (trie-insert-append syms filename v)
                                                    (trie-insert i v (term-def (def-params s ps) (qualif-term q t) (qualif-type q tp) , (filename , p)))
                                                    symb-occs

ctxt-term-udef : posinfo → defScope → var → term → ctxt → ctxt
ctxt-term-udef p s v t (mk-ctxt (filename , ps , q) syms i symb-occs) = mk-ctxt (filename , ps , qualif-insert-params q v ps)
                                                    (trie-insert-append syms filename v)
                                                    (trie-insert i v (term-udef (def-params s ps) (qualif-term q t) , (filename , p)))
                                                    symb-occs

ctxt-var-decl : posinfo → var → ctxt → ctxt
ctxt-var-decl p v (mk-ctxt (filename , ps , q) syms i symb-occs) = mk-ctxt (filename , ps , q)
                                                    (trie-insert-append syms filename v)
                                                    (trie-insert i v (var-decl , (filename , p)))
                                                    symb-occs

-- TODO not sure how this and renaming interacts with module scope
ctxt-var-decl-if : posinfo → var → ctxt → ctxt
ctxt-var-decl-if p v Γ with Γ
... | mk-ctxt (filename , ps , q) syms i symb-occs with trie-lookup i v
... | just (rename-def _ , _) = Γ
... | just (var-decl , _) = Γ
... | _ = mk-ctxt (filename , ps , q) (trie-insert-append syms filename v)
  (trie-insert i v (var-decl , (filename , p)))
  symb-occs

ctxt-rename-rep : ctxt → var → var
ctxt-rename-rep (mk-ctxt m syms i _) v with trie-lookup i v 
...                                           | just (rename-def v' , _) = v'
...                                           | _ = v

-- we assume that only the left variable might have been renamed
ctxt-eq-rep : ctxt → var → var → 𝔹
ctxt-eq-rep Γ x y = (ctxt-rename-rep Γ x) =string y

{- add a renaming mapping the first variable to the second, unless they are equal.
   Notice that adding a renaming for v will overwrite any other declarations for v. -}
ctxt-rename : posinfo → var → var → ctxt → ctxt
ctxt-rename p v v' (mk-ctxt (filename , ps , q) syms i symb-occs) = 
  (mk-ctxt (filename , ps , q) (trie-insert-append syms filename v)
      (trie-insert i v (rename-def v' , (filename , p)))
      symb-occs)

ctxt-tk-decl : posinfo → var → tk → ctxt → ctxt
ctxt-tk-decl p x (Tkt t) Γ = ctxt-term-decl p x t Γ 
ctxt-tk-decl p x (Tkk k) Γ = ctxt-type-decl p x k Γ 

----------------------------------------------------------------------
-- lookup functions
----------------------------------------------------------------------

-- look for a kind for the given var, which is assumed to be a type
ctxt-lookup-type-var : ctxt → var → maybe kind
ctxt-lookup-type-var (mk-ctxt _ _ i _) v with trie-lookup i v
...                                      | just (type-decl k , _) = just k
...                                      | just (type-def _ _ k , _) = just k
...                                      | _ = nothing

ctxt-lookup-term-var : ctxt → var → maybe type
ctxt-lookup-term-var (mk-ctxt _ _ i _) v with trie-lookup i v
...                                      | just (term-decl t , _) = just t
...                                      | just (term-def _ _ t , _) = just t
...                                      | _ = nothing

ctxt-lookup-var-tk : ctxt → var → maybe tk
ctxt-lookup-var-tk (mk-ctxt _ _ i _) v with trie-lookup i v
...                                     | just (type-decl k , _) = just (Tkk k)
...                                     | just (type-def _ _ k , _) = just (Tkk k)
...                                     | just (term-decl t , _) = just (Tkt t)
...                                     | just (term-def _ _ t , _) = just (Tkt t)
...                                     | _ = nothing

ctxt-lookup-kind-var : ctxt → var → 𝔹
ctxt-lookup-kind-var (mk-ctxt _ _ i _) v with trie-lookup i v
...                                      | just (kind-def _ _ _ , _) = tt
...                                      | _ = ff

ctxt-lookup-term-var-def : ctxt → var → maybe term
ctxt-lookup-term-var-def (mk-ctxt _ _ i _) v with trie-lookup i v
...                                           | just (term-def _ t _ , _) = just t
...                                           | just (term-udef _ t , _) = just t
...                                           | _ = nothing

ctxt-lookup-type-var-def : ctxt → var → maybe type
ctxt-lookup-type-var-def (mk-ctxt _ _ i _) v with trie-lookup i v
...                                          | just (type-def _ t _ , _) = just t
...                                          | _ = nothing

ctxt-lookup-kind-var-def : ctxt → var → maybe (params × kind)
ctxt-lookup-kind-var-def (mk-ctxt _ _ i _) x with trie-lookup i x
...                                          | just (kind-def _ ps k , _) = just (ps , k)
...                                          | _ = nothing

ctxt-binds-var : ctxt → var → 𝔹
ctxt-binds-var (mk-ctxt _ _ i _) x = trie-contains i x

ctxt-defines-var : ctxt → var → 𝔹
ctxt-defines-var (mk-ctxt _ _ i _) x with trie-lookup i x
...                                  | just (term-def _ _ _ , _) = tt
...                                  | just (term-udef _ _ , _) = tt
...                                  | just (type-def _ _ _ , _) = tt
...                                  | just (kind-def _ _ _ , _) = tt
...                                  | _ = ff

ctxt-declares-term-var : ctxt → var → 𝔹
ctxt-declares-term-var (mk-ctxt _ _ i _) x with trie-lookup i x
...                                  | just (term-decl _ , _) = tt
...                                  | _ = ff

ctxt-declares-type-var : ctxt → var → 𝔹
ctxt-declares-type-var (mk-ctxt _ _ i _) x with trie-lookup i x
...                                  | just (type-decl _ , _) = tt
...                                  | _ = ff

ctxt-lookup-occurrences : ctxt → var → 𝕃 (var × posinfo × string)
ctxt-lookup-occurrences (mk-ctxt _ _ _ symb-occs) symbol with trie-lookup symb-occs symbol
...                                                   | just l = l
...                                                   | nothing = []

----------------------------------------------------------------------

ctxt-var-location : ctxt → var → location
ctxt-var-location (mk-ctxt _ _ i _) x with trie-lookup i x
...                                   | just (_ , l) = l
...                                   | nothing = "missing" , "missing"


ctxt-set-current-file : ctxt → string → ctxt
ctxt-set-current-file (mk-ctxt _ syms i symb-occs) filename = mk-ctxt (filename , ParamsNil , empty-trie) syms i symb-occs

ctxt-clear-symbol : ctxt → string → ctxt
ctxt-clear-symbol (mk-ctxt f syms i symb-occs) x = mk-ctxt f (trie-remove syms x) (trie-remove i x) symb-occs

ctxt-clear-symbols : ctxt → 𝕃 string → ctxt
ctxt-clear-symbols Γ [] = Γ
ctxt-clear-symbols Γ (v :: vs) = ctxt-clear-symbols (ctxt-clear-symbol Γ v) vs

ctxt-clear-symbols-of-file : ctxt → (filename : string) → ctxt
ctxt-clear-symbols-of-file (mk-ctxt f syms i symb-occs) filename = mk-ctxt f (trie-insert syms filename [])
                                                                  (hremove i (trie-lookup𝕃 syms filename))
                                                                  symb-occs
  where hremove : ∀ {A : Set} → trie A → 𝕃 string → trie A
        hremove i [] = i
        hremove i (x :: xs) = hremove (trie-remove i x) xs

ctxt-initiate-file : ctxt → (filename : string) → ctxt
ctxt-initiate-file Γ filename = ctxt-set-current-file (ctxt-clear-symbols-of-file Γ filename) filename

ctxt-get-current-filename : ctxt → string
ctxt-get-current-filename (mk-ctxt (filename , _) _ _ _) = filename

ctxt-get-symbol-occurrences : ctxt → trie (𝕃 (var × posinfo × string))
ctxt-get-symbol-occurrences (mk-ctxt _ _ _ symb-occs) = symb-occs

ctxt-set-symbol-occurrences : ctxt → trie (𝕃 (var × posinfo × string)) → ctxt
ctxt-set-symbol-occurrences (mk-ctxt filename syms i symb-occs) new-symb-occs = mk-ctxt filename syms i new-symb-occs

