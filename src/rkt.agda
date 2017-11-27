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
to-rkt-var : var → string
to-rkt-var = 𝕃char-to-string
             ∘ ((map λ c → if c =char '\'' then '.' else c)
             ∘ string-to-𝕃char)

-- convert an erased Cedille term to string representation of a Racket term
to-rkt : term → string
to-rkt (Lam _ KeptLam _ v _ tm)
  = "(lambda (" ^ to-rkt-var v ^ ")" ^ (to-rkt tm) ^ ")"
-- untested
to-rkt (Let _ (DefTerm _ v _ tm-def) tm-body)
  = "(let ([" ^ to-rkt-var v ^ " " ^ to-rkt tm-def ^"]) " ^ to-rkt tm-body ^ ")\n"
to-rkt (Var _ v)
  = to-rkt-var v
to-rkt (App tm₁ x tm₂)
  = "(" ^ to-rkt tm₁ ^ " " ^ to-rkt tm₂ ^ ")" --"; no app\n"
to-rkt (Hole x)
  = "(error 'cedille-hole)"
to-rkt (Beta _ NoTerm)
  = "(lambda (x) x)\n"
to-rkt _
  = ""

rkt-erase-h : string → sym-info → string
-- unimplemented code path
rkt-erase-h n (term-def (just (ParamsCons (Decl _ _ v _ _) ps)) tm ty , fp , pi)
  = "; " ^ v ^ "\n"
-- the only tested code path
rkt-erase-h n (term-def (just ParamsNil) tm ty , fp , pi)
  = "(define " ^ n ^ (to-rkt tm) ^ ")\n"
-- unimplemented code path
rkt-erase-h n (term-def nothing tm ty , fp , pi)
  = "; TODO typed term-def (no params)\n"
-- untested code path
rkt-erase-h n (term-udef dp tm , fp , pi)
  = "(define " ^ n ^ (to-rkt tm) ^ ")\n"
rkt-erase-h _ (ctxt-info , (string , posinfo))
  = ""

-- in reverse order: lookup symbol defs from file,
-- pair name with info, and convert to racket
rkt-erase : ctxt → (ced-path : string)  → string
rkt-erase (mk-ctxt _ syms i sym-occurences) ced-path
  = foldr (λ l₁ l₂ → l₁ ^  l₂) ""
          (map (λ {(n , s) → rkt-erase-h n s})
          (reverse (drop-nothing
          (map (λ name → maybe-map (λ sinfo → name , sinfo)
               (trie-lookup i name))
          (snd (trie-lookup𝕃2 syms ced-path))))))

-- Erases the ced file at the given ced-path,
-- producing a .rkt file in a .racket subdirectory
write-rkt-file : (ced-path : string) → ctxt  → IO ⊤
write-rkt-file ced-path ctxt = 
  let dir = takeDirectory ced-path in
    createDirectoryIfMissing tt (dot-racket-directory dir) >>
    writeFile (rkt-filename ced-path)
              ("#lang racket\n\n" ^ rkt-erase ctxt ced-path) 
