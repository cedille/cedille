module spans where

open import lib
open import cedille-types 
open import syntax-util
open import to-string

--------------------------------------------------
-- tagged values, which go in spans
--------------------------------------------------
tagged-val : Set
tagged-val = string × string

tagged-val-to-string : tagged-val → string
tagged-val-to-string (tag , val) = "\"" ^ tag ^ "\":\"" ^ val ^ "\""

--------------------------------------------------
-- span datatype
--------------------------------------------------
data span : Set where
  mk-span : string → posinfo → posinfo → 𝕃 tagged-val {- extra information for the span -} → span

span-to-string : span → string
span-to-string (mk-span name start end extra) = 
  "[\"" ^ name ^ "\"," ^ start ^ "," ^ end ^ ",{" 
        ^ string-concat-sep-map "," tagged-val-to-string extra ^ "}]"

data spans : Set where
  regular-spans : 𝕃 span → spans
  global-error : string {- error message -} → maybe span → spans

global-error-p : spans → 𝔹
global-error-p (global-error _ _) = tt
global-error-p _ = ff

empty-spans : spans
empty-spans = regular-spans []

spans-to-string : spans → string
spans-to-string (regular-spans ss) = "{\"spans\":[" ^ (string-concat-sep-map "," span-to-string ss) ^ "]}\n"
spans-to-string (global-error e o) = "{\"error\":\"" ^ e ^ helper o ^ "\"" ^ "}\n"
  where helper : maybe span → string
        helper (just x) = ", \"global-error\":" ^ span-to-string x
        helper nothing = ""

add-span : span → spans → spans
add-span s (regular-spans ss) = regular-spans (s :: ss)
add-span s (global-error e e') = global-error e e'

--------------------------------------------------
-- spanM, a state monad for spans
--------------------------------------------------
spanM : Set → Set
spanM A = spans → A × spans

-- return for the spanM monad
spanMr : ∀{A : Set} → A → spanM A
spanMr a ss = a , ss

spanMok : spanM ⊤
spanMok = spanMr triv

infixl 2 _≫span_ _≫=span_ _≫=spanj_ _≫=spanm_

_≫=span_ : ∀{A B : Set} → spanM A → (A → spanM B) → spanM B
(m ≫=span m') c with m c
(m ≫=span m') _ | v , c = m' v c

_≫span_ : ∀{A : Set} → spanM ⊤ → spanM A → spanM A
(m ≫span m') c = m' (snd (m c))

_≫=spanj_ : ∀{A : Set} → spanM (maybe A) → (A → spanM ⊤) → spanM ⊤
_≫=spanj_{A} m m' = m ≫=span cont
  where cont : maybe A → spanM ⊤
        cont nothing = spanMok
        cont (just x) = m' x

_≫=spanm_ : ∀{A : Set} → spanM (maybe A) → (A → spanM (maybe A)) → spanM (maybe A)
_≫=spanm_{A} m m' = m ≫=span cont
  where cont : maybe A → spanM (maybe A)
        cont nothing = spanMr nothing
        cont (just a) = m' a

spanM-add : span → spanM ⊤
spanM-add s ss = triv , add-span s ss

--------------------------------------------------
-- tagged-val constants
--------------------------------------------------

explain-name : string
explain-name = "explanation"

expected-type : type → tagged-val
expected-type tp = "expected-type" , type-to-string tp

expected-kind : kind → tagged-val
expected-kind tp = "expected kind" , kind-to-string tp

missing-type : tagged-val
missing-type = "type" , "[undeclared]"

missing-kind : tagged-val
missing-kind = "kind" , "[undeclared]"

head-kind : kind → tagged-val
head-kind k = "the kind of the head" , kind-to-string k

type-app-head : type → tagged-val
type-app-head tp = "the head" , type-to-string tp

term-argument : term → tagged-val
term-argument t = "the argument" , term-to-string t

type-data : type → tagged-val
type-data tp = "type" , type-to-string tp 

kind-data : kind → tagged-val
kind-data k = "kind" , kind-to-string k

error-data : string → tagged-val
error-data s = "error" , s

tk-data : tk → tagged-val
tk-data (Tkk k) = kind-data k
tk-data (Tkt t) = type-data t

--------------------------------------------------
-- span-creating functions
--------------------------------------------------

Rec-name : string
Rec-name = "Rec"

Rec-explain : string → tagged-val
Rec-explain datatype-name = (explain-name , "Definition of recursive datatype " ^ datatype-name)

Star-name : string
Star-name = "Star"

parens-span : posinfo → posinfo → span
parens-span pi pi' = mk-span "parentheses" pi pi' []

data decl-class : Set where
  param : decl-class
  index : decl-class 

decl-class-name : decl-class → string
decl-class-name param = "parameter"
decl-class-name index = "index"

Decl-span : decl-class → posinfo → var → tk → posinfo → span
Decl-span dc pi v atk pi' = mk-span ((if tk-is-type atk then "Term " else "Type ") ^ (decl-class-name dc))
                                      pi pi' []

Ctordecl-span : posinfo → var → type → posinfo → span
Ctordecl-span pi x t pi' = mk-span "Constructor declaration" pi pi' []

TpVar-span : string → posinfo → 𝕃 tagged-val → span
TpVar-span v pi tvs = mk-span "Type variable" pi (posinfo-plus-str pi v) tvs

TpAppt-span : type → term → 𝕃 tagged-val → span
TpAppt-span tp t tvs = mk-span "Application of a type to a term" (type-start-pos tp) (term-end-pos t) tvs

TpQuant-e = 𝔹

is-pi : TpQuant-e
is-pi = tt

TpQuant-span : TpQuant-e → posinfo → var → tk → type → 𝕃 tagged-val → span
TpQuant-span is-pi pi x atk body tvs = mk-span (if is-pi then "Dependent function type" else "Implicit dependent function type")
                                         pi (type-end-pos body) tvs

TpLambda-span : posinfo → var → tk → type → 𝕃 tagged-val → span
TpLambda-span pi x atk body tvs = mk-span "Type-level lambda abstraction" pi (type-end-pos body) tvs

-- a span boxing up the parameters and the indices of a Rec definition
RecPrelim-span : string → posinfo → posinfo → span
RecPrelim-span name pi pi' = mk-span ("Parameters, indices, and constructor declarations for datatype " ^ name) pi pi' []

TpArrow-span : type → type → 𝕃 tagged-val → span
TpArrow-span t1 t2 tvs = mk-span "Arrow type" (type-start-pos t1) (type-end-pos t2) tvs
