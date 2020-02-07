import cedille-options
open import general-util

module toplevel-state (options : cedille-options.options) {mF : Set → Set} {{_ : monad mF}} where

open import cedille-types
--open import classify options {mF}
open import ctxt
open import constants
open import rename
open import spans options {mF}
open import syntax-util
open import to-string options
open import string-format
open import subst
open import json

import cws-types

record include-elt : Set where
  field ast : maybe ex-file
        ast~ : maybe file
        cwst : maybe cws-types.start
        deps : 𝕃 string -- dependencies
        import-to-dep : trie filepath -- map import strings in the file to their full paths
        ss : spans ⊎ string -- spans in string form (read from disk)
        err : 𝔹 -- is ss reporting an error
        need-to-add-symbols-to-context : 𝔹
        do-type-check : 𝔹
        inv : do-type-check imp need-to-add-symbols-to-context ≡ tt
        last-parse-time : maybe UTC
        cede-up-to-date : 𝔹
        rkt-up-to-date : 𝔹
        source : string

blank-include-elt : include-elt
blank-include-elt = record { ast = nothing ; ast~ = nothing; cwst = nothing; deps = [] ;
                             import-to-dep = empty-trie ; ss = inj₂ "" ; err = ff ; need-to-add-symbols-to-context = tt ;
                             do-type-check = tt ; inv = refl ; last-parse-time = nothing; cede-up-to-date = ff ; rkt-up-to-date = ff ; source = "" }

-- the dependencies should pair import strings found in the file with the full paths to those imported files
new-include-elt : filepath → (dependencies : 𝕃 (string × string)) → (ast : ex-file) →
                  cws-types.start → maybe UTC → include-elt
new-include-elt filename deps x y time =
  record { ast = just x ; ast~ = nothing; cwst = just y ; deps = map snd deps ; import-to-dep = trie-fill empty-trie deps ; ss = inj₂ "" ; err = ff ;
           need-to-add-symbols-to-context = tt ;
           do-type-check = tt ; inv = refl ; last-parse-time = time ; cede-up-to-date = ff ; rkt-up-to-date = ff ; source = "" }

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

set-spans-include-elt : include-elt → spans → file → include-elt
set-spans-include-elt ie ss f = 
 record ie { ss = inj₁ ss ; 
             ast~ = just f ;
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

set-source-include-elt : include-elt → string → include-elt
set-source-include-elt ie source = record ie { source = source }

record toplevel-state : Set where
  constructor mk-toplevel-state
  field include-path : 𝕃 string × stringset
        files-with-updated-spans : 𝕃 string
        is : trie include-elt {- keeps track of files we have parsed and/or processed -}
        Γ : ctxt
        logFilePath : filepath

new-toplevel-state : (logFilePath : filepath) → (include-path : 𝕃 string × stringset) → toplevel-state
new-toplevel-state logFilePath ip =
  record { include-path = ip ;
           files-with-updated-spans = [] ;
           is = empty-trie ;
           Γ = new-ctxt "[nofile]" "[nomod]" ;
           logFilePath = logFilePath }
                                                                             
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

include-elt-spans-to-json : include-elt → json
include-elt-spans-to-json ie with (include-elt.ss ie)
include-elt-spans-to-json ie | inj₁ ss = spans-to-json ss
include-elt-spans-to-json ie | inj₂ ss = json-raw [[ ss ]]

include-elt-to-archive : include-elt → json
include-elt-to-archive ie with (include-elt.ss ie) | (include-elt.source ie)
include-elt-to-archive ie | inj₁ ss | source = json-object $ ("source" , json-string source) :: spans-to-json' ss
include-elt-to-archive ie | inj₂ ss | source = json-object $ ("source" , json-string source) :: [ "spans" , json-raw [[ ss ]] ]

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

params-to-string''' : params → string
params-to-string''' [] = ""
-- TODO print erased vs non-erased?
params-to-string''' (Param me v tk :: pms) = "{var: " ^ v ^ ", tk: " ^ rope-to-string (tpkd-to-string empty-ctxt tk) ^ "}" ^ ", " ^ (params-to-string''' pms)

defParams-to-string : defParams → string
defParams-to-string (just pms) = params-to-string''' pms
defParams-to-string nothing = ""

-- TODO also print modname?
syms-to-string : trie (string × 𝕃 string) → string
syms-to-string = trie-to-string ", " (λ l → "{" ^ (𝕃-to-string (λ s → s) ", " (snd l)) ^ "}")

ctxt-info-to-string : ctxt-info → string
ctxt-info-to-string (term-decl tp) = "term-decl: {type: " ^ rope-to-string (to-string empty-ctxt tp) ^ "}"
ctxt-info-to-string (term-def dp opac t tp) = "term-def: {defParams: {" ^ (defParams-to-string dp) ^ "}, opacity: " ^ (opacity-to-string opac) ^ ", maybe term: " ^ maybe-else' t "nothing" (λ t → "just " ^ rope-to-string (to-string empty-ctxt t)) ^ ", type: " ^ rope-to-string (to-string empty-ctxt tp) ^ "}"
ctxt-info-to-string (term-udef dp opac t) = "term-udef: {defParams: {" ^ (defParams-to-string dp) ^ "}, opacity: " ^ (opacity-to-string opac) ^ ", term: " ^ rope-to-string (to-string empty-ctxt t) ^ "}"
ctxt-info-to-string (type-decl k) = "type-decl: {kind: " ^ rope-to-string (to-string empty-ctxt k) ^ "}"
ctxt-info-to-string (type-def dp opac tp k) = "type-def: {defParams: {" ^ (defParams-to-string dp) ^ "}, opacity: " ^ (opacity-to-string opac) ^ ", maybe type: " ^ maybe-else' tp "nothing" (λ tp → "just " ^ rope-to-string (to-string empty-ctxt tp)) ^ ", kind: " ^ rope-to-string (to-string empty-ctxt k) ^ "}"
ctxt-info-to-string (kind-def pms k) = "kind-def: {pms: " ^ (params-to-string''' pms) ^ "kind: " ^ rope-to-string (to-string empty-ctxt k) ^ "}"
ctxt-info-to-string (rename-def v) = "rename-def: {var: " ^ v ^ "}"
ctxt-info-to-string (var-decl) = "var-decl"
ctxt-info-to-string (ctr-def _ _ _ _ _) = "ctr-def"
--ctxt-info-to-string (mu-def x) = "mu-def: {var: " ^ x ^ "}"
--ctxt-info-to-string (datatype-def ps kᵢ k cs) = "datatype-def: {defParams: {" ^ defParams-to-string ps ^ "}, inductive hypothesis kind: " ^ rope-to-string (to-string empty-ctxt kᵢ) ^ ", kind: " ^ rope-to-string (to-string empty-ctxt k) ^ ", cs: " ^ "TODO" ^ "}"
--ctxt-info-to-string (mu-def ps x k) = "mu-def: {defParams: {" ^ defParams-to-string ps ^ "}, datatype var: " ^ x ^ ", kind: " ^ rope-to-string (to-string empty-ctxt k) ^ "}"

sym-info-to-string : sym-info → string
sym-info-to-string (ci , (fn , pi)) = "{ctxt-info: " ^ (ctxt-info-to-string ci) ^ ", location: {filename: " ^ fn ^ ", posinfo: " ^ pi ^ "}}"

sym-infos-to-string : trie sym-info → string
sym-infos-to-string = trie-to-string ", " sym-info-to-string

occ-to-string : var × posinfo × string → string
occ-to-string (v , pi , s) = "var: " ^ v ^ ", posinfo: " ^ pi ^ ", string: " ^ s

sym-occs-to-string : trie (𝕃 (var × posinfo × string)) → string
sym-occs-to-string = trie-to-string ", " (λ l → "{" ^ (𝕃-to-string occ-to-string ", " l) ^ "}")

qualif-to-string : qualif-info → string
qualif-to-string (x , as) = x ^ rope-to-string (doc-to-rope $ fst (args-to-string as {TERM} NIL 0 [] (new-ctxt "" "") nothing neither)) where open import pretty

mod-info-to-string : (string × string × params × qualif) → string
mod-info-to-string (fn , mn , pms , q) = "filename: " ^ fn ^ ", modname: " ^ mn ^ ", pms: {" ^ (params-to-string''' pms) ^ "}" ^ ", qualif: {" ^ (trie-to-string ", " qualif-to-string q) ^ "}"

ctxt-to-string : ctxt → string
ctxt-to-string (mk-ctxt fn mn ps qual syms mod-map _ _ _ is _ _ _ _ _ _) = "mod-info: {" ^ (mod-info-to-string (fn , mn , ps , qual)) ^ "}, syms: {" ^ (syms-to-string syms) ^ "}, i: {" ^ (sym-infos-to-string is) ^ "}"

toplevel-state-to-string : toplevel-state → string
toplevel-state-to-string (mk-toplevel-state include-path files is context logFilePath) =
    "\ninclude-path: {\n" ^ (𝕃-to-string (λ x → x) "\n" (fst include-path)) ^ 
    "\n}\nis: {" ^ (trie-to-string "\n" include-elt-to-string is) ^ 
    "\n}\nΓ: {" ^ (ctxt-to-string context) ^
    "\n}\nlogFilePath : {" ^ logFilePath ^ "\n}"
    

-- check if a variable is being redefined, and if so return the first given state; otherwise the second (in the monad)
check-redefined : ∀ {X} → posinfo → var → toplevel-state → X → spanM toplevel-state → spanM (toplevel-state × X)
check-redefined pi v s x c =
  let Γ = toplevel-state.Γ s in
  if ctxt-binds-var Γ v then
    ([- redefined-var-span Γ pi v -] return2 s x)
  else (c >>= λ s → return2 s x)

import-as-x : var → maybe var → var
import-as-x v nothing = v
import-as-x v (just pfx) = pfx # v

error-in-import-string = "There is an error in the imported file"

-- Traverse all imports, returning an error if we encounter the same file twice
{-# TERMINATING #-}
check-cyclic-imports : (original current : filepath) → stringset → (path : 𝕃 string) → toplevel-state → err-m
check-cyclic-imports fnₒ fn fs path s with stringset-contains fs fn
...| ff = foldr (λ fnᵢ x → x ||-maybe check-cyclic-imports fnₒ fnᵢ (stringset-insert fs fn) (fn :: path) s)
            nothing (include-elt.deps (get-include-elt s fn))
...| tt with fnₒ =string fn
...| tt = just (foldr (λ fnᵢ x → x ^ " → " ^ fnᵢ) ("Cyclic dependencies (" ^ fn) path ^ " → " ^ fn ^ ")")
...| ff = just error-in-import-string

scope-t : Set → Set
scope-t X = filepath → string → maybe var → params → args → X → toplevel-state → toplevel-state × err-m

infixl 0 _>>=scope_
_>>=scope_ : toplevel-state × err-m → (toplevel-state → toplevel-state × err-m) → toplevel-state × err-m
_>>=scope_ (ts , err) f with f ts
...| ts' , err' = ts' , err ||-maybe err'

{-# TERMINATING #-}
scope-file : toplevel-state → (original imported : filepath) → maybe var → args → toplevel-state × err-m
scope-file' : scope-t ⊤
scope-cmds : scope-t cmds
scope-cmd : scope-t cmd
scope-var : scope-t var
scope-ctrs : scope-t ctrs
scope-datatype-names : scope-t var
scope-enc-defs : scope-t encoding-defs

scope-file ts fnₒ fnᵢ oa as with check-cyclic-imports fnₒ fnᵢ (trie-single fnₒ triv) [] ts
...| just e = ts , just e
...| nothing = scope-file' fnₒ fnᵢ oa [] as triv ts

scope-file' fnₒ fn oa psₒ as triv s with get-include-elt s fn
...| ie with include-elt.err ie | include-elt.ast~ ie
...| e | nothing = s , when e error-in-import-string
...| e | just (Module mn ps cs) =
  (s , when e error-in-import-string) >>=scope
  scope-cmds fn mn oa ps as cs

scope-cmds fn mn oa ps as (c :: cs) s =
  scope-cmd fn mn oa ps as c s >>=scope scope-cmds fn mn oa ps as cs
scope-cmds fn mn oa ps as [] s = s , nothing

scope-cmd fn mn oa ps as (CmdImport (Import Private ifn mn' oa' as')) s = s , nothing
scope-cmd fn mn oa psₒ asₒ (CmdImport (Import Public ifn mn' oa' asᵢ')) s =
  scope-file' fn ifn oa psₒ asᵢ triv s
  -- ^ oa' should be NoOptAs, so we can use oa ^
  where

  merged : trie (maybe arg) → params → args → trie (maybe arg)
  merged σ (Param me x tk :: ps) (a :: as) =
    merged (trie-insert σ x $ just a) ps as
  merged σ (Param me x tk :: ps) [] =
    merged (trie-insert σ x nothing) ps []
  merged σ _ _ = σ
  
  arg-var : arg → maybe var
  arg-var (Arg (Var x)) = just x
  arg-var (ArgE (Ttm (Var x))) = just x
  arg-var (ArgE (Ttp (TpVar x))) = just x
  arg-var _ = nothing

  σ = merged empty-trie psₒ asₒ
  
  reorder : args → args
  reorder (a :: as) =
    maybe-else' (arg-var a >>= trie-lookup σ) (a :: reorder as) λ ma →
    maybe-else' ma [] λ a → a :: reorder as
  reorder [] = []
  
  asᵢ = reorder asᵢ'

scope-cmd fn mn oa ps as (CmdDefKind v _ _) = scope-var fn mn oa ps as v
scope-cmd fn mn oa ps as (CmdDefTerm v   _) = scope-var fn mn oa ps as v
scope-cmd fn mn oa ps as (CmdDefType v _ _) = scope-var fn mn oa ps as v
scope-cmd fn mn oa ps as (CmdDefData eds v _ _ cs) s =
  scope-var fn mn oa ps as v s >>=scope
  scope-ctrs fn mn oa ps as cs >>=scope
  scope-enc-defs fn mn oa ps as eds >>=scope
  scope-datatype-names fn mn oa ps as v

scope-ctrs fn mn oa ps as [] s = s , nothing
scope-ctrs fn mn oa ps as (Ctr x T :: ds) s =
  scope-var fn mn oa ps as x s >>=scope
  scope-ctrs fn mn oa ps as ds

scope-datatype-names fn mn oa ps as x s =
  scope-var fn mn oa ps as (data-Is/ x) s >>=scope
  scope-var fn mn oa ps as (data-is/ x) >>=scope
  scope-var fn mn oa ps as (data-to/ x)

scope-enc-defs fn mn oa ps as eds s =
  record s { Γ = record (toplevel-state.Γ s) { μᵤ = just eds } } , nothing


scope-var fn mn oa ps as ignored-var s = s , nothing
scope-var _ mn oa ps as v s with import-as-x v oa | s
...| v' | mk-toplevel-state ip fns is Γ logFilePath =
  mk-toplevel-state ip fns is
    (record Γ { qual = trie-insert (ctxt.qual Γ) v' (mn # v , as) }) logFilePath ,
  flip maybe-map (trie-lookup (ctxt.qual Γ) v') (uncurry λ v'' as' →
    "Multiple definitions of variable " ^ v' ^ " as " ^ v'' ^ " and " ^ (mn # v) ^
    (if (mn # v =string v'') then " (perhaps it was already imported?)" else ""))
