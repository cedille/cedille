module rkt where

open import string
open import char
open import io
open import maybe
open import ctxt
open import list
open import trie
open import general-util
open import unit
open import bool
open import functions
open import product
open import cedille-types
open import syntax-util

private
  rkt-dbg-flag = tt

  rkt-dbg : string → string → string
  rkt-dbg msg out = (if rkt-dbg-flag then ("; " ^ msg ^ "\n") else "") ^ out

dot-racket-directory : string → string 
-- constructs the name of a .racket directory for the given original directory
dot-racket-directory dir = combineFileNames dir ".racket"

rkt-filename : (ced-path : string) → string
-- constructs the fully-qualified name of a .rkt file for a .ced file at the given ced-path
rkt-filename ced-path = 
  let dir = takeDirectory ced-path in
  let unit-name = base-filename (takeFileName ced-path) in
    combineFileNames (dot-racket-directory dir) (unit-name ^ ".rkt")

-- Racket does not allow "'" as part of a legal identifier.
-- Swamp this out for "."
rkt-iden : var → var
rkt-iden = 𝕃char-to-string
           ∘ ((map λ c → if c =char '\'' then '.' else c)
           ∘ string-to-𝕃char)

-- convert an erased Cedille term to string representation of a Racket term
rkt-from-term : term → string
rkt-from-term (Lam _ KeptLam _ v _ tm)
  = "(lambda (" ^ rkt-iden v ^ ")" ^ (rkt-from-term tm) ^ ")"
-- untested
rkt-from-term (Let _ (DefTerm _ v _ tm-def) tm-body)
  = "(let ([" ^ rkt-iden v ^ " " ^ rkt-from-term tm-def ^"]) "
          ^ rkt-from-term tm-body ^ ")\n"
rkt-from-term (Var _ v)
  = rkt-iden v
rkt-from-term (App tm₁ x tm₂)
  = "(" ^ rkt-from-term tm₁ ^ " " ^ rkt-from-term tm₂ ^ ")"
rkt-from-term (Hole x)
  = "(error 'cedille-hole)"
rkt-from-term (Beta _ NoTerm)
  = "(lambda (x) x)\n"
rkt-from-term _
  = rkt-dbg "unsupported/unknown term" ""

rkt-define : string → term → string
rkt-define name tm = "(define " ^ name ^ (rkt-from-term tm) ^ ")"

rkt-from-sym-info : string → sym-info → string
rkt-from-sym-info n (term-def (just (ParamsCons (Decl _ _ v _ _) _)) tm ty , _)
  -- TODO not tested
  = rkt-dbg "term-def: paramsCons:" (rkt-define n tm)
rkt-from-sym-info n (term-def (just ParamsNil) tm ty , _)
  = rkt-dbg "term-def: paramsNil:"  (rkt-define n tm)
rkt-from-sym-info n (term-def nothing tm ty , b)
  -- TODO not tested
  = rkt-dbg "term-def: nothing:"    (rkt-define n tm)
rkt-from-sym-info n (term-udef _ tm , _)
  = rkt-dbg "term-udef:"            (rkt-define n tm)
rkt-from-sym-info n (term-decl x , _)
  = rkt-dbg "term-decl"             ""
rkt-from-sym-info n (type-decl x , _)
  = rkt-dbg "type-decl:"            ""
rkt-from-sym-info n (type-def _ _ _ , _)
  = rkt-dbg "type-def:"             ""
rkt-from-sym-info n (kind-def _ _ _ , _)
  = rkt-dbg "kind-def:"             ""
rkt-from-sym-info n (rename-def v , _)
  -- TODO Not implemented!
  = rkt-dbg ("rename-def: " ^ v)    ""
rkt-from-sym-info n (var-decl , _)
  = rkt-dbg "var-decl:"             ""

-- Erases the ced file at the given ced-path,
-- producing a .rkt file in a .racket subdirectory
write-rkt-file : (ced-path : string) → ctxt  → IO ⊤
write-rkt-file ced-path (mk-ctxt _ syms i sym-occurences) = 
  let dir = takeDirectory ced-path
  in createDirectoryIfMissing tt (dot-racket-directory dir) >>
     writeFile (rkt-filename ced-path)
               (rkt-header ^ rkt-body)

  where
  cdle-mod  = fst (trie-lookup𝕃2 syms ced-path)
  cdle-defs = snd (trie-lookup𝕃2 syms ced-path)

  qual-name : string → string
  qual-name name = cdle-mod ^ "." ^ name

  rkt-header rkt-body : string
  rkt-header = "#lang racket\n\n"

  -- in reverse order: lookup symbol defs from file,
  -- pair name with info, and convert to racket
  rkt-body   = string-concat-sep "\n"
               (map (λ { (n , s) → rkt-from-sym-info (qual-name n) s})
               (reverse (drop-nothing
               (map (λ name →
                       maybe-map (λ syminf → name , syminf)
                                 (trie-lookup i (qual-name name)))
               cdle-defs))))
