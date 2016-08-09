module toplevel-state where

open import lib

open import cedille-types
open import classify
open import ctxt
open import constants
open import conversion
open import general-util
open import rec
open import spans
open import syntax-util
open import to-string

import cws-types

record include-elt : Set where
  field ast : maybe start
        cwst : maybe cws-types.start
        deps : (𝕃 string) {- dependencies -}
        import-to-dep : trie string {- map import strings in the file to their full paths -}
        ss : string {- spans in string form, either from ones we compute now or read from disk -}
        err : 𝔹 -- is ss reporting an error
        need-to-add-symbols-to-context : 𝔹 
        do-type-check : 𝔹
        inv : do-type-check imp need-to-add-symbols-to-context ≡ tt

blank-include-elt : include-elt
blank-include-elt = record { ast = nothing ; cwst = nothing; deps = [] ; 
                             import-to-dep = empty-trie ; ss = "" ; err = ff ; need-to-add-symbols-to-context = tt ; 
                             do-type-check = tt ; inv = refl }

-- the dependencies should pair import strings found in the file with the full paths to those imported files
new-include-elt : (filename : string) → (dependencies : 𝕃 (string × string)) → (ast : start) →
                  cws-types.start → include-elt
new-include-elt filename deps x y =
  record { ast = just x ; cwst = just y ; deps = map snd deps ; import-to-dep = trie-fill empty-trie deps ; ss = "" ; err = ff ;
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
        files-with-updated-spans : 𝕃 string
        is : trie include-elt {- keeps track of files we have parsed and/or processed -}
        Γ : ctxt

new-toplevel-state : (include-path : 𝕃 string) → toplevel-state
new-toplevel-state ip = record { include-path = ip ; files-with-updated-spans = [] ; is = empty-trie ; 
                                 Γ = new-ctxt "[nofile]" }

get-include-elt-if : toplevel-state → (filename : string) → maybe include-elt
get-include-elt-if s filename = trie-lookup (toplevel-state.is s) filename

-- get an include-elt assuming it will be there
get-include-elt : toplevel-state → (filename : string) → include-elt
get-include-elt s filename with get-include-elt-if s filename
get-include-elt s filename | nothing = blank-include-elt {- should not happen -}
get-include-elt s filename | just ie = ie

set-include-elt : toplevel-state → string → include-elt → toplevel-state 
set-include-elt s f ie = record s { is = trie-insert (toplevel-state.is s) f ie }

set-include-path : toplevel-state → 𝕃 string → toplevel-state 
set-include-path s ip = record s { include-path = ip }

get-do-type-check : toplevel-state → string → 𝔹
get-do-type-check s filename = include-elt.do-type-check (get-include-elt s filename)

