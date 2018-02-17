module toplevel-state where

open import lib

open import cedille-types
open import classify
open import ctxt
open import constants
open import conversion
open import general-util
open import spans
open import syntax-util
open import to-string

import cws-types

record include-elt : Set where
  field ast : maybe start
        cwst : maybe cws-types.start
        deps : (𝕃 string) {- dependencies -}
        import-to-dep : trie string {- map import strings in the file to their full paths -}
        ss : spans ⊎ string {- spans in string form (read from disk) -}
        err : 𝔹 -- is ss reporting an error
        need-to-add-symbols-to-context : 𝔹 
        do-type-check : 𝔹
        inv : do-type-check imp need-to-add-symbols-to-context ≡ tt

blank-include-elt : include-elt
blank-include-elt = record { ast = nothing ; cwst = nothing; deps = [] ; 
                             import-to-dep = empty-trie ; ss = inj₂ "" ; err = ff ; need-to-add-symbols-to-context = tt ; 
                             do-type-check = tt ; inv = refl }

-- the dependencies should pair import strings found in the file with the full paths to those imported files
new-include-elt : (filename : string) → (dependencies : 𝕃 (string × string)) → (ast : start) →
                  cws-types.start → include-elt
new-include-elt filename deps x y =
  record { ast = just x ; cwst = just y ; deps = map snd deps ; import-to-dep = trie-fill empty-trie deps ; ss = inj₂ "" ; err = ff ;
           need-to-add-symbols-to-context = tt ; 
           do-type-check = tt ; inv = refl }

error-include-elt : string → include-elt
error-include-elt err = record blank-include-elt { ss = inj₂ (global-error-string err) ; err = tt }

error-span-include-elt : string → posinfo → include-elt
error-span-include-elt err pos = record blank-include-elt { ss = inj₁ (add-span (span.mk-span err pos (posinfo-plus pos 1) [ error-data "" ] ) empty-spans ) ; err = tt }

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
 record ie { ss = inj₁ ss ; 
             err = spans-have-error ss  }

set-spans-string-include-elt : include-elt → (err : 𝔹) → string → include-elt
set-spans-string-include-elt ie err ss = record ie { ss = inj₂ ss ; err = err  }

record toplevel-state : Set where
  constructor mk-toplevel-state
  field use-cede-files : 𝔹
        make-rkt-files : 𝔹
        include-path : 𝕃 string
        files-with-updated-spans : 𝕃 string
        is : trie include-elt {- keeps track of files we have parsed and/or processed -}
        Γ : ctxt

new-toplevel-state : (include-path : 𝕃 string) → (should-use-cede-files : 𝔹) → (should-make-rkt-files : 𝔹)  → toplevel-state
new-toplevel-state ip should-use-cede-files should-make-rkt-files = record { use-cede-files = should-use-cede-files ; make-rkt-files = should-make-rkt-files ; include-path = ip ;
                                                                             files-with-updated-spans = [] ; is = empty-trie ; Γ = new-ctxt "[nofile]" "[nomod]" }
                                                                             
toplevel-state-lookup-occurrences : var → toplevel-state → 𝕃 (var × posinfo × string)
toplevel-state-lookup-occurrences symb (mk-toplevel-state _ _ _ _ _ Γ) = ctxt-lookup-occurrences Γ symb

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

include-elt-spans-to-streeng : include-elt → streeng
include-elt-spans-to-streeng ie with (include-elt.ss ie)
include-elt-spans-to-streeng ie | inj₁ ss = spans-to-streeng ss
include-elt-spans-to-streeng ie | inj₂ ss = [[ ss ]]

include-elt-to-string : include-elt → string
include-elt-to-string ie =
    " deps:  " ^ (𝕃-to-string (λ x → x) "," (include-elt.deps ie)) ^
    -- ast
    " import-to-dep:  " ^ (trie-to-string "," (λ x → x) (include-elt.import-to-dep ie)) ^ 
    -- spans
    " err:  " ^ (𝔹-to-string (include-elt.err ie)) ^ 
    ", need-to-add-symbols-to-context:  " ^ (𝔹-to-string (include-elt.need-to-add-symbols-to-context ie)) ^
    ", do-type-check:  " ^ (𝔹-to-string (include-elt.do-type-check ie)) ^
    " "

eΓ : ctxt
eΓ = new-ctxt "" ""

params-to-string : params → string
params-to-string ParamsNil = ""
params-to-string (ParamsCons (Decl pi pi' v t-k pi'') pms) = "{var: " ^ v ^ ", tk: " ^ streeng-to-string (tk-to-string empty-ctxt t-k) ^ "}" ^ ", " ^ (params-to-string pms)

defParams-to-string : defParams → string
defParams-to-string (just pms) = params-to-string pms
defParams-to-string nothing = ""

-- TODO also print modname?
syms-to-string : trie (string × 𝕃 string) → string
syms-to-string = trie-to-string ", " (λ l → "{" ^ (𝕃-to-string (λ s → s) ", " (snd l)) ^ "}")

ctxt-info-to-string : ctxt-info → string
ctxt-info-to-string (term-decl tp) = "term-decl: {type: " ^ streeng-to-string (to-string empty-ctxt tp) ^ "}"
ctxt-info-to-string (term-def dp t tp) = "term-def: {defParams: {" ^ (defParams-to-string dp) ^ "}, term: " ^ streeng-to-string (to-string empty-ctxt t) ^ ", type: " ^ streeng-to-string (to-string empty-ctxt tp) ^ "}"
ctxt-info-to-string (term-udef dp t) = "term-udef: {defParams: {" ^ (defParams-to-string dp) ^ "}, term: " ^ streeng-to-string (to-string empty-ctxt t) ^ "}"
ctxt-info-to-string (type-decl k) = "type-decl: {kind: " ^ streeng-to-string (to-string empty-ctxt k) ^ "}"
ctxt-info-to-string (type-def dp tp k) = "type-def: {defParams: {" ^ (defParams-to-string dp) ^ "}, tp: " ^ streeng-to-string (to-string empty-ctxt tp) ^ ", kind: " ^ streeng-to-string (to-string empty-ctxt k) ^ "}"
ctxt-info-to-string (kind-def pms pms' k) = "kind-def: {pms: " ^ (params-to-string pms) ^ ", pms': " ^ (params-to-string pms') ^ "kind: " ^ streeng-to-string (to-string empty-ctxt k) ^ "}"
ctxt-info-to-string (rename-def v) = "rename-def: {var: " ^ v ^ "}"
ctxt-info-to-string (var-decl) = "var-decl"

sym-info-to-string : sym-info → string
sym-info-to-string (ci , (fn , pi)) = "{ctxt-info: " ^ (ctxt-info-to-string ci) ^ ", location: {filename: " ^ fn ^ ", posinfo: " ^ pi ^ "}}"

sym-infos-to-string : trie sym-info → string
sym-infos-to-string = trie-to-string ", " sym-info-to-string

occ-to-string : var × posinfo × string → string
occ-to-string (v , pi , s) = "var: " ^ v ^ ", posinfo: " ^ pi ^ ", string: " ^ s

sym-occs-to-string : trie (𝕃 (var × posinfo × string)) → string
sym-occs-to-string = trie-to-string ", " (λ l → "{" ^ (𝕃-to-string occ-to-string ", " l) ^ "}")

qualif-to-string : qualif-info → string
qualif-to-string (x , as) = x ^ streeng-to-string (fst (args-to-string as {TERM} [[]] 0 [] (new-ctxt "" "") nothing neither))

mod-info-to-string : mod-info → string
mod-info-to-string (fn , mn , pms , q) = "filename: " ^ fn ^ ", modname: " ^ mn ^ ", pms: {" ^ (params-to-string pms) ^ "}" ^ ", qualif: {" ^ (trie-to-string ", " qualif-to-string q) ^ "}"

ctxt-to-string : ctxt → string
ctxt-to-string (mk-ctxt mi ss is os) = "mod-info: {" ^ (mod-info-to-string mi) ^ "}, syms: {" ^ (syms-to-string ss) ^ "}, i: {" ^ (sym-infos-to-string is) ^ "}, sym-occs: {" ^ (sym-occs-to-string os) ^ "}"

toplevel-state-to-string : toplevel-state → string
toplevel-state-to-string (mk-toplevel-state use-cede-file make-rkt-file include-path files-with-updated-spans is context) =
    "use-cede-file: " ^ (𝔹-to-string use-cede-file) ^
    "\nmake-rkt-file: " ^ (𝔹-to-string make-rkt-file) ^
    "\ninclude-path: {\n\r" ^ (𝕃-to-string (λ x → x) "\n\r" include-path) ^ 
    "\n}\nfiles-with-updated-spans: {\n\r" ^ (𝕃-to-string (λ x → x) "\n\r" files-with-updated-spans) ^ 
    "\n}\nis: {" ^ (trie-to-string "\n\r" include-elt-to-string is) ^ 
    "\n}\nΓ: {" ^ (ctxt-to-string context) ^ "}"

-- check if a variable is being redefined, and if so return the first given state; otherwise the second (in the monad)
check-redefined : posinfo → var → toplevel-state → spanM toplevel-state → spanM toplevel-state
check-redefined pi x s c =
  get-ctxt (λ Γ →
    if ctxt-binds-var Γ x then
      (spanM-add (redefined-var-span Γ pi x) ≫span spanMr s)
    else c)

scope-imports : toplevel-state → string → optAs → args → toplevel-state
scope-imports s import-fn oa as with toplevel-state.Γ s
... | mk-ctxt (fn , mn , ps , q) syms i symb-occs with trie-lookup syms import-fn
... | nothing = s
... | just (import-mn , vs) = let q' = qualif-insert-import q import-mn oa vs as in
  record s { Γ = mk-ctxt (fn , mn , ps , q') syms i symb-occs }

