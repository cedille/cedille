import cedille-options

module rkt (options : cedille-options.options) where

open import general-util
open import ctxt-types
open import toplevel-state options {IO}
open import unit
open import bool
open import functions
open import product
open import cedille-types
open import syntax-util

private
  rkt-dbg-flag = ff

  rkt-dbg : string → rope → rope
  rkt-dbg msg out = [[ if rkt-dbg-flag then ("; " ^ msg ^ "\n") else "" ]] ⊹⊹ out

-- constructs the name of a .racket directory for the given original directory
rkt-dirname : string → string 
rkt-dirname dir = combineFileNames dir ".racket"

-- constructs the fully-qualified name of a .rkt file for a .ced file at the given ced-path
{-rkt-filename : (ced-path : string) → string
rkt-filename ced-path = 
  let dir = takeDirectory ced-path in
  let unit-name = base-filename (takeFileName ced-path) in
    combineFileNames (rkt-dirname dir) (unit-name ^ ".rkt")-}

-- sanitize a Cedille identifier for Racket
-- Racket does not allow "'" as part of a legal identifier,
-- so swamp this out for "."
rkt-iden : var → var
rkt-iden = 𝕃char-to-string
           ∘ ((map λ c → if c =char '\'' then '.' else c)
           ∘ string-to-𝕃char)

-- Racket string from erase Cedile term
rkt-from-term : term → rope
rkt-from-term (Lam ff v _ tm)
  = [[ "(lambda (" ]] ⊹⊹ [[ rkt-iden v ]] ⊹⊹ [[ ")" ]] ⊹⊹ rkt-from-term tm ⊹⊹ [[ ")" ]]
-- TODO untested
rkt-from-term (LetTm ff v _ tm-def tm-body)
  = [[ "(let ([" ]] ⊹⊹ [[ rkt-iden v ]] ⊹⊹ [[ " " ]] ⊹⊹ rkt-from-term tm-def ⊹⊹ [[ "]) " ]] ⊹⊹ rkt-from-term tm-body ⊹⊹ [[ ")\n" ]]
rkt-from-term (Var v)
  = [[ rkt-iden v ]]
rkt-from-term (App tm₁ tm₂)
  = [[ "(" ]] ⊹⊹ rkt-from-term tm₁ ⊹⊹ [[ " " ]] ⊹⊹ rkt-from-term tm₂ ⊹⊹ [[ ")" ]]
rkt-from-term (Hole x)
  = [[ "(error 'cedille-hole)" ]]
rkt-from-term _
  = rkt-dbg "unsupported/unknown term" [[]]

-- Racket define form from var, term
rkt-define : var → term → rope
rkt-define v tm = [[ "(define " ]] ⊹⊹ [[ rkt-iden v ]] ⊹⊹ rkt-from-term tm ⊹⊹ [[ ")" ]] ⊹⊹ [[ "\n" ]]

-- Racket require form from file
rkt-require-file : string → rope
rkt-require-file fp = [[ "(require (file \"" ]] ⊹⊹ [[ fp ]] ⊹⊹ [[ "\"))" ]]

-- Racket term from Cedille term sym-info
rkt-from-sym-info : string → sym-info → rope
rkt-from-sym-info n (term-def (just (Param _ v _ :: _)) _ (just tm) ty , _)
  -- TODO not tested
  = rkt-dbg "term-def: paramsCons:" (rkt-define n tm)
rkt-from-sym-info n (term-def _ _ nothing ty , b)
  = rkt-dbg "term-def: def nothing" [[]]
rkt-from-sym-info n (term-def (just ParamsNil) _ (just tm) ty , _)
  = rkt-dbg "term-def: paramsNil:"  (rkt-define n tm)
rkt-from-sym-info n (term-def nothing _ (just tm) ty , b)
  -- TODO not tested
  = rkt-dbg "term-def: nothing:"    (rkt-define n tm)
rkt-from-sym-info n (term-udef _ _ tm , _)
  = rkt-dbg "term-udef:"            (rkt-define n tm)
rkt-from-sym-info n (term-decl x , _)
  = rkt-dbg "term-decl"             [[]]
rkt-from-sym-info n (type-decl x , _)
  = rkt-dbg "type-decl:"            [[]]
rkt-from-sym-info n (type-def _ _ _ _ , _)
  = rkt-dbg "type-def:"             [[]]
rkt-from-sym-info n (kind-def _ _ , _)
  = rkt-dbg "kind-def:"             [[]]
rkt-from-sym-info n (rename-def v , _)
  -- TODO Not implemented!
  = rkt-dbg ("rename-def: " ^ v)    [[]]
rkt-from-sym-info n (var-decl , _)
  = rkt-dbg "var-decl:"             [[]]
rkt-from-sym-info n (ctr-def _ _ _ _ _ , _) 
  = rkt-dbg "const-def:"           [[]]
--rkt-from-sym-info n (datatype-def _ _ _ _ , _) 
--  = rkt-dbg "datatype-def:"           [[]]
--rkt-from-sym-info n (mu-def ps x k , _)
--  = rkt-dbg "mu-def:" [[]]

to-rkt-file : (ced-path : string) → ctxt → include-elt → ((cede-filename : string) → string) → rope
to-rkt-file ced-path Γ ie rkt-filename =
  rkt-header ⊹⊹ rkt-body
  where
  cdle-pair = trie-lookup𝕃2 (ctxt.syms Γ) ced-path
  cdle-mod  = fst cdle-pair
  cdle-defs = snd cdle-pair

  qual-name : string → string
  qual-name name = cdle-mod ^ "." ^ name

  -- lang pragma, imports, and provides
  rkt-header rkt-body : rope
  rkt-header =
    [[ "#lang racket\n\n" ]] ⊹⊹
    foldr (λ fn x → rkt-require-file (rkt-filename fn) ⊹⊹ x)
      [[ "\n" ]] (include-elt.deps ie) ⊹⊹
    [[ "(provide (all-defined-out))\n\n" ]]

  -- in reverse order: lookup symbol defs from file,
  -- pair name with info, and convert to racket
  rkt-body   = foldr (λ {(n , s) x → x ⊹⊹
                        [[ "\n" ]] ⊹⊹ rkt-from-sym-info (qual-name n) s}) [[]]
               (drop-nothing (map
                 (λ name → maybe-map (λ syminf → name , syminf)
                   (trie-lookup (ctxt.i Γ) (qual-name name)))
                 cdle-defs))
{-
-- write a Racket file to .racket subdirectory from Cedille file path,
-- context, and include-elt
write-rkt-file : (ced-path : string) → ctxt → include-elt → ((cede-filename : string) → string) → IO ⊤
write-rkt-file ced-path (mk-ctxt _ (syms , _) i sym-occurences) ie rkt-filename =
  let dir = takeDirectory ced-path
  in createDirectoryIfMissing tt (rkt-dirname dir) >>
     writeFile (rkt-filename ced-path)
               (rkt-header ^ rkt-body)

  where
  cdle-mod  = fst (trie-lookup𝕃2 syms ced-path)
  cdle-defs = snd (trie-lookup𝕃2 syms ced-path)

  qual-name : string → string
  qual-name name = cdle-mod ^ "." ^ name

  -- lang pragma, imports, and provides
  rkt-header rkt-body : string
  rkt-header = "#lang racket\n\n"
               ^ (string-concat-sep "\n"
                   (map (rkt-require-file ∘ rkt-filename)
                   (include-elt.deps ie))) ^ "\n"
               ^ "(provide (all-defined-out))\n\n"

  -- in reverse order: lookup symbol defs from file,
  -- pair name with info, and convert to racket
  rkt-body   = string-concat-sep "\n"
               (map (λ { (n , s) → rkt-from-sym-info (qual-name n) s})
               (reverse (drop-nothing
               (map (λ name →
                       maybe-map (λ syminf → name , syminf)
                                 (trie-lookup i (qual-name name)))
               cdle-defs))))
-}
