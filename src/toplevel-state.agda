import cedille-options
open import general-util

module toplevel-state (options : cedille-options.options) {mF : Set → Set} {{_ : monad mF}} where

open import lib

open import cedille-types
open import classify options {mF}
open import ctxt
open import constants
open import conversion
open import rename
open import spans options {mF}
open import syntax-util
open import to-string options
open import string-format
open import subst

import cws-types

record include-elt : Set where
  field ast : maybe start
        cwst : maybe cws-types.start
        deps : 𝕃 string {- dependencies -}
        import-to-dep : trie string {- map import strings in the file to their full paths -}
        ss : spans ⊎ string {- spans in string form (read from disk) -}
        err : 𝔹 -- is ss reporting an error
        need-to-add-symbols-to-context : 𝔹 
        do-type-check : 𝔹
        inv : do-type-check imp need-to-add-symbols-to-context ≡ tt
        last-parse-time : maybe UTC
        cede-up-to-date : 𝔹
        rkt-up-to-date : 𝔹

blank-include-elt : include-elt
blank-include-elt = record { ast = nothing ; cwst = nothing; deps = [] ; 
                             import-to-dep = empty-trie ; ss = inj₂ "" ; err = ff ; need-to-add-symbols-to-context = tt ; 
                             do-type-check = tt ; inv = refl ; last-parse-time = nothing; cede-up-to-date = ff ; rkt-up-to-date = ff }

-- the dependencies should pair import strings found in the file with the full paths to those imported files
new-include-elt : filepath → (dependencies : 𝕃 (string × string)) → (ast : start) →
                  cws-types.start → maybe UTC → include-elt
new-include-elt filename deps x y time =
  record { ast = just x ; cwst = just y ; deps = map snd deps ; import-to-dep = trie-fill empty-trie deps ; ss = inj₂ "" ; err = ff ;
           need-to-add-symbols-to-context = tt ; 
           do-type-check = tt ; inv = refl ; last-parse-time = time ; cede-up-to-date = ff ; rkt-up-to-date = ff }

error-include-elt : string → include-elt
error-include-elt err = record blank-include-elt { ss = inj₂ (global-error-string err) ; err = tt }

error-span-include-elt : string → string → posinfo → include-elt
error-span-include-elt err errSpan pos = record blank-include-elt { ss = inj₁ (add-span (span.mk-span err pos (posinfo-plus pos 1) [] (just errSpan) ) empty-spans ) ; err = tt }

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

set-last-parse-time-include-elt : include-elt → UTC → include-elt
set-last-parse-time-include-elt ie time =
  record ie { last-parse-time = just time }

set-cede-file-up-to-date-include-elt : include-elt → 𝔹 → include-elt
set-cede-file-up-to-date-include-elt ie up-to-date = record ie { cede-up-to-date = up-to-date }
set-rkt-file-up-to-date-include-elt : include-elt → 𝔹 → include-elt
set-rkt-file-up-to-date-include-elt ie up-to-date = record ie { rkt-up-to-date = up-to-date }

set-spans-string-include-elt : include-elt → (err : 𝔹) → string → include-elt
set-spans-string-include-elt ie err ss = record ie { ss = inj₂ ss ; err = err  }

record toplevel-state : Set where
  constructor mk-toplevel-state
  field include-path : 𝕃 string × stringset
        files-with-updated-spans : 𝕃 string
        is : trie include-elt {- keeps track of files we have parsed and/or processed -}
        Γ : ctxt

new-toplevel-state : (include-path : 𝕃 string × stringset) → toplevel-state
new-toplevel-state ip = record { include-path = ip ;
                                                                             files-with-updated-spans = [] ; is = empty-trie ; Γ = new-ctxt "[nofile]" "[nomod]" }
                                                                             
toplevel-state-lookup-occurrences : var → toplevel-state → 𝕃 (var × posinfo × string)
toplevel-state-lookup-occurrences symb (mk-toplevel-state _ _ _ Γ) = ctxt-lookup-occurrences Γ symb

get-include-elt-if : toplevel-state → filepath → maybe include-elt
get-include-elt-if s filename = trie-lookup (toplevel-state.is s) filename

-- get an include-elt assuming it will be there
get-include-elt : toplevel-state → filepath → include-elt
get-include-elt s filename with get-include-elt-if s filename
get-include-elt s filename | nothing = blank-include-elt {- should not happen -}
get-include-elt s filename | just ie = ie


set-include-elt : toplevel-state → filepath → include-elt → toplevel-state 
set-include-elt s f ie = record s { is = trie-insert (toplevel-state.is s) f ie }

set-include-path : toplevel-state → 𝕃 string × stringset → toplevel-state 
set-include-path s ip = record s { include-path = ip }

get-do-type-check : toplevel-state → string → 𝔹
get-do-type-check s filename = include-elt.do-type-check (get-include-elt s filename)

include-elt-spans-to-rope : include-elt → rope
include-elt-spans-to-rope ie with (include-elt.ss ie)
include-elt-spans-to-rope ie | inj₁ ss = spans-to-rope ss
include-elt-spans-to-rope ie | inj₂ ss = [[ ss ]]

include-elt-to-string : include-elt → string
include-elt-to-string ie =
    " deps:  " ^ (𝕃-to-string (λ x → x) "," (include-elt.deps ie)) ^
    -- ast
    ", ast:  " ^ maybe-else "not parsed" (λ ast → "parsed") (include-elt.ast ie) ^ ", " ^
    " import-to-dep:  " ^ (trie-to-string "," (format "filename: %s") (include-elt.import-to-dep ie)) ^ 
    -- spans
    " err:  " ^ (𝔹-to-string (include-elt.err ie)) ^ 
    ", need-to-add-symbols-to-context:  " ^ (𝔹-to-string (include-elt.need-to-add-symbols-to-context ie)) ^
    ", do-type-check:  " ^ (𝔹-to-string (include-elt.do-type-check ie)) ^
    ", last-parse-time: " ^ (maybe-else "" utcToString (include-elt.last-parse-time ie))

params-to-string'' : params → string
params-to-string'' ParamsNil = ""
-- TODO print erased vs non-erased?
params-to-string'' (ParamsCons (Decl pi pi' me v t-k pi'') pms) = "{var: " ^ v ^ ", tk: " ^ rope-to-string (tk-to-string empty-ctxt t-k) ^ "}" ^ ", " ^ (params-to-string'' pms)

defParams-to-string : defParams → string
defParams-to-string (just pms) = params-to-string'' pms
defParams-to-string nothing = ""

-- TODO also print modname?
syms-to-string : trie (string × 𝕃 string) → string
syms-to-string = trie-to-string ", " (λ l → "{" ^ (𝕃-to-string (λ s → s) ", " (snd l)) ^ "}")

ctxt-info-to-string : ctxt-info → string
ctxt-info-to-string (term-decl tp) = "term-decl: {type: " ^ rope-to-string (to-string empty-ctxt tp) ^ "}"
ctxt-info-to-string (term-def dp t tp) = "term-def: {defParams: {" ^ (defParams-to-string dp) ^ "}, term: " ^ rope-to-string (to-string empty-ctxt t) ^ ", type: " ^ rope-to-string (to-string empty-ctxt tp) ^ "}"
ctxt-info-to-string (term-udef dp t) = "term-udef: {defParams: {" ^ (defParams-to-string dp) ^ "}, term: " ^ rope-to-string (to-string empty-ctxt t) ^ "}"
ctxt-info-to-string (type-decl k) = "type-decl: {kind: " ^ rope-to-string (to-string empty-ctxt k) ^ "}"
ctxt-info-to-string (type-def dp tp k) = "type-def: {defParams: {" ^ (defParams-to-string dp) ^ "}, tp: " ^ rope-to-string (to-string empty-ctxt tp) ^ ", kind: " ^ rope-to-string (to-string empty-ctxt k) ^ "}"
ctxt-info-to-string (kind-def pms pms' k) = "kind-def: {pms: " ^ (params-to-string'' pms) ^ ", pms': " ^ (params-to-string'' pms') ^ "kind: " ^ rope-to-string (to-string empty-ctxt k) ^ "}"
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
qualif-to-string (x , as) = x ^ rope-to-string (fst (args-to-string as {TERM} [[]] 0 [] (new-ctxt "" "") nothing neither))

mod-info-to-string : mod-info → string
mod-info-to-string (fn , mn , pms , q) = "filename: " ^ fn ^ ", modname: " ^ mn ^ ", pms: {" ^ (params-to-string'' pms) ^ "}" ^ ", qualif: {" ^ (trie-to-string ", " qualif-to-string q) ^ "}"

ctxt-to-string : ctxt → string
ctxt-to-string (mk-ctxt mi (ss , mn-fn) is os) = "mod-info: {" ^ (mod-info-to-string mi) ^ "}, syms: {" ^ (syms-to-string ss) ^ "}, i: {" ^ (sym-infos-to-string is) ^ "}, sym-occs: {" ^ (sym-occs-to-string os) ^ "}"

toplevel-state-to-string : toplevel-state → string
toplevel-state-to-string (mk-toplevel-state include-path files is context) =
    "\ninclude-path: {\n" ^ (𝕃-to-string (λ x → x) "\n" (fst include-path)) ^ 
    "\n}\nis: {" ^ (trie-to-string "\n" include-elt-to-string is) ^ 
    "\n}\nΓ: {" ^ (ctxt-to-string context) ^ "}"

-- check if a variable is being redefined, and if so return the first given state; otherwise the second (in the monad)
check-redefined : posinfo → var → toplevel-state → spanM toplevel-state → spanM toplevel-state
check-redefined pi x s c =
  get-ctxt (λ Γ →
    if ctxt-binds-var Γ x then
      (spanM-add (redefined-var-span Γ pi x) ≫span spanMr s)
    else c)

{-
scope-imports : toplevel-state → string → optAs → args → toplevel-state
scope-imports s import-fn oa as with toplevel-state.Γ s
... | mk-ctxt (fn , mn , ps , q) (syms , mn-fn) i symb-occs with trie-lookup syms import-fn
... | nothing = s
... | just (import-mn , vs) = let q' = qualif-insert-import q import-mn oa vs as in
  record s { Γ = mk-ctxt (fn , mn , ps , q') (syms , mn-fn) i symb-occs }
-}

import-as : var → optAs → var
import-as v NoOptAs = v
import-as v (SomeOptAs pi pfx) = pfx # v

{-# TERMINATING #-}
scope-file : toplevel-state → filepath → optAs → args → toplevel-state
scope-cmds : toplevel-state → filepath → (mn : string) → cmds → optAs → args → toplevel-state
scope-cmd : toplevel-state → filepath → (mn : string) → cmd → optAs → args → toplevel-state
scope-def : toplevel-state → filepath → (mn : string) → var → optAs → args → toplevel-state
scope-public-args : toplevel-state → (old-fp new-fp : filepath) → args → args → args

scope-file s fn oa as with include-elt.ast (get-include-elt s fn)
...| nothing = s
...| just (File pi0 is pi1 pi2 mn ps cs pi3) =
  scope-cmds (scope-cmds s fn mn (imps-to-cmds is) oa as) fn mn cs oa as

scope-cmds s fn mn (CmdsNext c cs) oa as =
  scope-cmds (scope-cmd s fn mn c oa as) fn mn cs oa as
scope-cmds s fn mn CmdsStart oa as = s

scope-cmd s fn mn (ImportCmd (Import pi NotPublic pi' ifn oa' as' pi'')) oa as = s
scope-cmd s fn mn (ImportCmd (Import pi IsPublic pi' ifn oa' as' pi'')) oa as =
  let ifn' = trie-lookup-else ifn (include-elt.import-to-dep (get-include-elt s fn)) ifn in
  scope-file s ifn' oa' (scope-public-args s fn ifn' as as')
scope-cmd s fn mn (DefKind pi v ps k pi') oa as = scope-def s fn mn v oa as
scope-cmd s fn mn (DefTermOrType (DefTerm pi v mcT t) pi') oa as = scope-def s fn mn v oa as
scope-cmd s fn mn (DefTermOrType (DefType pi v k T) pi') oa as = scope-def s fn mn v oa as

scope-def (mk-toplevel-state ip fns is (mk-ctxt (mn' , fn , pms , q) ss sis os)) _ mn v oa as =
  mk-toplevel-state ip fns is
    (mk-ctxt (mn' , fn , pms , trie-insert q (import-as v oa) (mn # v , as)) ss sis os)

-- For importing a file (foo) that publicly imports another file (bar),
-- we need to substitute the arguments given to foo for occurences of foo's
-- parameters in the arguments to bar
scope-public-args s ofn nfn as as' with lookup-mod-params (toplevel-state.Γ s) ofn
...| nothing = as'
...| just ps = flip uncurry (get-sub ps as) λ ρt ρT →
               substh-args (toplevel-state.Γ s) empty-renamectxt ρT
               (substh-args (toplevel-state.Γ s) empty-renamectxt ρt as)
  where
  get-sub : params → args → trie term × trie type
  get-sub (ParamsCons (Decl _ _ me x atk _) ps) (ArgsCons a as) =
    flip uncurry (get-sub ps as) λ ρt ρT → case a of λ where
      (TermArg me' t) → trie-insert ρt x t , ρT
      (TypeArg T) → ρt , trie-insert ρT x T
  get-sub ps as = empty-trie , empty-trie
