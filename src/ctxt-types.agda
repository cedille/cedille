module ctxt-types where

open import cedille-types
open import general-util
open import syntax-util

location : Set
location = string × posinfo -- file path and starting position in the file 

-- file path and starting / ending position in file
span-location = string × posinfo × posinfo

-- missing locations
missing-location : location
missing-location = ("missing" , "missing")

missing-span-location : span-location
missing-span-location = ("missing" , "missing" , "missing")

{- we will generally keep classifiers of variables in hnf in the ctxt, although
   we will not necessarily unfold recursive type definitions. -}

defScope : Set
defScope = 𝔹
pattern localScope = tt
pattern globalScope = ff
pattern concrete-datatype = globalScope
pattern abstract-datatype = localScope

defParams : Set
defParams = maybe params

data ctxt-info : Set where
  -- for defining a datatype
--  datatype-def : defParams → (ind reg : kind) → ctrs → ctxt-info

  -- for defining a datatype constructor
  ctr-def : params → type → (ctrs-length ctr-index ctr-unerased-arrows : ℕ) → ctxt-info

  -- for declaring the type that proves a type is a datatype (X/Mu)
--  mu-def : defParams → var → kind → ctxt-info

  -- for declaring a variable to have a given type (with no definition)
  term-decl : type → ctxt-info

  -- for defining a variable to equal a term with a given type
  -- maybe term, because datatype X/Mu and X/mu have params, etc... but no def
  term-def : defParams → opacity → maybe term → type → ctxt-info

  -- for untyped term definitions 
  term-udef : defParams → opacity → term → ctxt-info

  -- for declaring a variable to have a given kind (with no definition)
  type-decl : kind → ctxt-info

  -- for defining a variable to equal a type with a given kind
  type-def : defParams → opacity → maybe type → kind → ctxt-info

  -- for defining a variable to equal a kind
  kind-def : params → kind → ctxt-info

  -- to rename a variable at any level to another
  rename-def : var → ctxt-info

  -- representing a declaration of a variable with no other information about it
  var-decl : ctxt-info

sym-info : Set
sym-info = ctxt-info × location

-- module filename, name, parameters, and qualifying substitution
mod-info : Set
mod-info = string × string × params × qualif

is-term-level : ctxt-info → 𝔹
is-term-level (term-decl _) = tt
is-term-level (term-def _ _ _ _) = tt
is-term-level (term-udef _ _ _) = tt
is-term-level (ctr-def _ _ _ _ _ ) = tt
is-term-level _ = ff

record ctxt : Set where
  constructor mk-ctxt
  field
    -- current module
    mod : mod-info

    -- filename → module name × symbols declared in that module,
    -- module name → filename × params,
    -- and file ID's for use in to-string.agda
    syms : trie (string × 𝕃 string) × trie string × trie params × trie ℕ × Σ ℕ (𝕍 string)

    -- symbols → ctxt-info × location
    i : trie sym-info

    -- concrete/global datatypes ×
    -- abstract/local datatypes ×
    -- datatype/Mu map ×
    -- highlighting datatypes
    Δ : trie (params × kind × kind × ctrs) × trie (var × var × args) × trie var × stringset


ctxt-binds-var : ctxt → var → 𝔹
ctxt-binds-var (mk-ctxt (_ , _ , _ , q) _ i _) x = trie-contains q x || trie-contains i x

ctxt-var-decl : var → ctxt → ctxt
ctxt-var-decl v (mk-ctxt (fn , mn , ps , q) syms i Δ) =
  mk-ctxt (fn , mn , ps , trie-insert q v (v , [])) syms (trie-insert i v (var-decl , "missing" , "missing")) Δ

ctxt-var-decl-loc : posinfo → var → ctxt → ctxt
ctxt-var-decl-loc pi v (mk-ctxt (fn , mn , ps , q) syms i Δ) =
  mk-ctxt (fn , mn , ps , trie-insert q v (v , [])) syms (trie-insert i v (var-decl , fn , pi)) Δ

qualif-var : ctxt → var → var
qualif-var (mk-ctxt (_ , _ , _ , q) _ _ _) v with trie-lookup q v
...| just (v' , _) = v'
...| nothing = v

start-modname : ex-file → string
start-modname (ExModule _ _ _ mn _ _ _) = mn

ctxt-get-current-filename : ctxt → string
ctxt-get-current-filename (mk-ctxt (fn , _) _ _ _) = fn

ctxt-get-current-mod : ctxt → mod-info
ctxt-get-current-mod (mk-ctxt m _ _ _) = m

ctxt-get-current-modname : ctxt → string
ctxt-get-current-modname (mk-ctxt (_ , mn , _ , _) _ _ _) = mn

ctxt-get-current-params : ctxt → params
ctxt-get-current-params (mk-ctxt (_ , _ , ps , _) _ _ _) = ps

