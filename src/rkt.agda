module rkt where

open import string
open import io
open import maybe
open import ctxt
open import list
open import trie
open import general-util
open import unit
open import bool
open import product
open import cedille-types


dot-racket-directory : string → string 
-- constructs the name of a .racket directory for the given original directory
dot-racket-directory dir = combineFileNames dir ".racket"

rkt-filename : (ced-path : string) → string
-- constructs the fully-qualified name of a .rkt file for a .ced file at the given ced-path
rkt-filename ced-path = 
  let dir = takeDirectory ced-path in
  let unit-name = base-filename (takeFileName ced-path) in
    combineFileNames (dot-racket-directory dir) (unit-name ^ ".rkt")

rkt-erase-h : sym-info → string
rkt-erase-h (ctxt-info , (string , posinfo)) = "TODO" -- find erase-term, in syntax-utils, and use to recurse down parse trees.

rkt-erase : ctxt → (ced-path : string)  → string
rkt-erase (mk-ctxt _ syms i sym-occurences) ced-path =  foldr (_^_) "" (map rkt-erase-h (drop-nothing (map (trie-lookup i) (trie-lookup𝕃 syms ced-path))))
    
    
write-rkt-file : (ced-path : string) → ctxt  → IO ⊤
-- Erases the ced file at the given ced-path, producing a .rkt file in a .racket subdirectory
write-rkt-file ced-path ctxt = 
  let dir = takeDirectory ced-path in
    createDirectoryIfMissing ff (dot-racket-directory dir) >>
    writeFile (rkt-filename ced-path) (rkt-erase ctxt ced-path) -- (ctxt-to-string ctxt) -- TODO fill with erased ced file content
