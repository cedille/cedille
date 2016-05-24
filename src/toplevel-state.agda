module toplevel-state where

open import lib

open import cedille-types
open import classify
open import ctxt
open import constants
open import conversion
open import rec
open import spans
open import syntax-util
open import to-string

record include-elt : Set where
  field path : string {- full path to the file for this named unit -}
        ast : maybe start 
        deps : (𝕃 string) {- dependencies -}
        ss : string {- spans in string form, either from ones we compute now or read from disk -}
        err : 𝔹 -- is ss reporting an error
        need-to-add-symbols-to-context : 𝔹 
        do-type-check : 𝔹
        inv : do-type-check imp need-to-add-symbols-to-context ≡ tt

blank-include-elt : include-elt
blank-include-elt = record { path = "" ; ast = nothing ; deps = [] ; ss = "" ; err = ff ; need-to-add-symbols-to-context = tt ; 
                             do-type-check = tt ; inv = refl }

{- this computes the deps from start -}
new-include-elt : (filename : string) → start → include-elt
new-include-elt filename x = record { path = filename ; ast = just x ; deps = compute-deps x ; ss = "" ; err = ff ;
                                      need-to-add-symbols-to-context = tt ; 
                                      do-type-check = tt ; inv = refl }

error-include-elt : string → include-elt
error-include-elt err = record blank-include-elt { ss = global-error-string err ; err = tt }

set-do-type-check-include-elt : include-elt → 𝔹 → include-elt
set-do-type-check-include-elt ie b = 
 record ie { need-to-add-symbols-to-context = (b || include-elt.need-to-add-symbols-to-context ie) ; 
             do-type-check = b ; 
             inv = lem b }
 where lem : (b : 𝔹) → b imp (b || include-elt.need-to-add-symbols-to-context ie) ≡ tt
       lem tt = refl
       lem ff = refl

set-need-to-add-symbols-to-context-include-elt : include-elt → 𝔹 → include-elt
set-need-to-add-symbols-to-context-include-elt ie b = 
 record ie { need-to-add-symbols-to-context = b ; 
             do-type-check = b && include-elt.do-type-check ie ; 
             inv = lem b }
 where lem : ∀(b : 𝔹){b' : 𝔹} → b && b' imp b ≡ tt
       lem tt {tt} = refl
       lem tt {ff} = refl
       lem ff {tt} = refl
       lem ff {ff} = refl

set-spans-include-elt : include-elt → spans → include-elt
set-spans-include-elt ie ss = 
 record ie { ss = spans-to-string ss ; 
             err = spans-have-error ss  }

set-spans-string-include-elt : include-elt → (err : 𝔹) → string → include-elt
set-spans-string-include-elt ie err ss = record ie { ss = ss ; err = err  }

record toplevel-state : Set where
  constructor mk-toplevel-state
  field include-path : 𝕃 string
        units-with-updated-spans : 𝕃 string
        is : trie include-elt {- keeps track of files we have parsed and/or processed -}
        Γ : ctxt

new-toplevel-state : (include-path : 𝕃 string) → toplevel-state
new-toplevel-state ip = record { include-path = ip ; units-with-updated-spans = [] ; is = empty-trie ; 
                                 Γ = new-ctxt "[nounit]" "[nofile]" }

get-include-elt-if : toplevel-state → (unit-name : string) → maybe include-elt
get-include-elt-if s unit-name = trie-lookup (toplevel-state.is s) unit-name

-- get an include-elt assuming it will be there
get-include-elt : toplevel-state → (unit-name : string) → include-elt
get-include-elt s unit-name with get-include-elt-if s unit-name
get-include-elt s unit-name | nothing = blank-include-elt {- should not happen -}
get-include-elt s unit-name | just ie = ie

set-include-elt : toplevel-state → string → include-elt → toplevel-state 
set-include-elt s f ie = record s { is = trie-insert (toplevel-state.is s) f ie }

set-include-path : toplevel-state → 𝕃 string → toplevel-state 
set-include-path s ip = record s { include-path = ip }

get-do-type-check : toplevel-state → string → 𝔹
get-do-type-check s unit-name = include-elt.do-type-check (get-include-elt s unit-name)

get-path-for-unit : toplevel-state → string → string
get-path-for-unit s unit-name = include-elt.path (get-include-elt s unit-name)
