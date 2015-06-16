module check where

open import lib

open import cedille-types
open import eqs
open import rename
open import syntax-util
open import tpstate

data evclass : Set where
  term-type : term → type → evclass
  type-kind : type → kind → evclass

-- local evidence context
evctxt : Set
evctxt = trie evclass

empty-evctxt : evctxt
empty-evctxt = empty-trie

evctxt-insert-tk : evctxt → string → string → tk → evctxt
evctxt-insert-tk Δ u x (Tkk k) = trie-insert Δ u (type-kind (Ltype (TpVar x)) k)
evctxt-insert-tk Δ u x (Tkt t) = trie-insert Δ u (term-type (Var x) t)

{- the return type for all the check functions.  The returned string is
   information for the user about holes. -}
check-return-t : Set
check-return-t = error-t string

unimplemented : string → check-return-t
unimplemented s = yes-error (s ^ " is currently unimplemented.")

check-term : tpstate → evctxt → evidence → term → type → check-return-t
check-type : tpstate → evctxt → evidence → type → kind → check-return-t  
check-ltypel : tpstate → evctxt → levidence → ltype → kind → check-return-t  
check-typel : tpstate → evctxt → levidence → type → kind → check-return-t  
check-ltype : tpstate → evctxt → evidence → ltype → kind → check-return-t  
check-tk : tpstate → evctxt → evidence → tk → check-return-t  
check-tkl : tpstate → evctxt → levidence → tk → check-return-t  
check-kind : tpstate → evctxt → evidence → kind → check-return-t  
check-kindl : tpstate → evctxt → levidence → kind → check-return-t  
check-term s Δ ev trm tp = yes-error "check-term not implemented"
check-type s Δ (Enu u u' (Pair e (Pair e' (Pair e'' e''')))) (Nu X k Θ T) k' with eq-kind s k k'
check-type s Δ (Enu u u' (Pair e (Pair e' (Pair e'' e''')))) (Nu X k Θ T) k' | tt = unimplemented "Checking nu-types"
check-type s Δ (Enu u u' (Pair e (Pair e' (Pair e'' e''')))) (Nu X k Θ T) k' | ff = 
  yes-error ("The kind of a nu-abstraction does not match the expected one.\n\n"
           ^ "1. The kind of the nu-abstraction: " ^ kind-to-string k ^ "\n"
           ^ "2. The expected kind " ^ kind-to-string k')
check-type s Δ e (Nu X k Θ T) k' = yes-error "Incorrect form of evidence for checking a nu-type." 
check-type s Δ e t k = unimplemented "Part of check-type"

check-typel s Δ e l t = unimplemented "Part of check-typel"

check-ltypel s Δ e l t = unimplemented "Part of check-ltypel"

check-kind s Δ (Xi u (EclassSome e) e') (KndPi x' a k) = check-tk s Δ e a ≫=err λ _ → check-kind s (evctxt-insert-tk Δ u x' a) e' k
check-kind s Δ (Xi _ (EclassSome e) e') (KndArrow k k') = check-kind s Δ e k ≫=err λ _ → check-kind s Δ e' k'
check-kind s Δ (Xi u (EclassSome e) e') (KndTpArrow t k') = check-ltype s Δ e t Star ≫=err λ _ → check-kind s Δ e' k'
check-kind s Δ e (KndParens k) = check-kind s Δ e k
check-kind s Δ (Levidence l) k = check-kindl s Δ l k 
check-kind s Δ e k = 
  yes-error ("Encountered the wrong form of evidence for checking the following kind:\n" ^ kind-to-string k)

check-kindl s Δ l (KndParens k) = check-kindl s Δ l k
check-kindl s Δ (Eparens e) k = check-kind s Δ e k
check-kindl s Δ (Earrow l l') (KndPi x' a k) = check-tkl s Δ l a ≫=err λ _ → check-kindl s Δ l' k
check-kindl s Δ (Earrow l l') (KndArrow k k') = check-kindl s Δ l k ≫=err λ _ → check-kindl s Δ l' k'
check-kindl s Δ (Earrow l l') (KndTpArrow t k') = check-ltypel s Δ l t Star ≫=err λ _ → check-kindl s Δ l' k'
check-kindl s Δ Check Star = no-error ""
check-kindl s Δ Ehole k = no-error (kind-to-string k ^ " ⇐ □\n")
check-kindl s Δ (EholeNamed n) k = no-error (n ^ " ∷ " ^ kind-to-string k ^ " ⇐ □\n")

check-kindl s Δ l k = unimplemented "Part of check-kindl"

check-tk s Δ e (Tkk k) = check-kind s Δ e k
check-tk s Δ e (Tkt t) = check-type s Δ e t Star

check-tkl s Δ l (Tkk k) = check-kindl s Δ l k
check-tkl s Δ l (Tkt t) = check-typel s Δ l t Star

check-ltype s Δ e l k = unimplemented "check-ltype"
