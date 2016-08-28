module spans where

open import lib
open import cedille-types 
open import conversion
open import ctxt
open import syntax-util
open import to-string

--------------------------------------------------
-- tagged values, which go in spans
--------------------------------------------------
tagged-val : Set
tagged-val = string × string

-- We number these when so we can sort them back in emacs
tagged-val-to-string : ℕ → tagged-val → string
tagged-val-to-string n (tag , val) = "\"" ^ tag ^ "\":\"" ^ ℕ-to-string n ^ " " ^ val ^ "\""

tagged-vals-to-string : ℕ → 𝕃 tagged-val → string
tagged-vals-to-string n [] = ""
tagged-vals-to-string n (s :: []) = tagged-val-to-string n s
tagged-vals-to-string n (s :: (s' :: ss)) = tagged-val-to-string n s ^ "," ^ tagged-vals-to-string (suc n) (s' :: ss)

--------------------------------------------------
-- span datatype
--
-- individual spans with an error message should
-- include a tagged-val with the tag "error"
-- (see is-error-span below)
--------------------------------------------------
data span : Set where
  mk-span : string → posinfo → posinfo → 𝕃 tagged-val {- extra information for the span -} → span

span-to-string : span → string
span-to-string (mk-span name start end extra) = 
  "[\"" ^ name ^ "\"," ^ start ^ "," ^ end ^ ",{" ^ tagged-vals-to-string 0 extra ^ "}]"

data spans : Set where
  regular-spans : 𝕃 span → spans
  global-error : string {- error message -} → maybe span → spans

is-error-span : span → 𝔹
is-error-span (mk-span _ _ _ tvs) = list-any (λ tv → (fst tv) =string "error") tvs

spans-have-error : spans → 𝔹
spans-have-error (regular-spans ss) = list-any is-error-span ss
spans-have-error (global-error _ _) = tt

empty-spans : spans
empty-spans = regular-spans []

global-error-string : string → string
global-error-string msg = "{\"error\":\"" ^ msg ^ "\"" ^ "}\n"

spans-to-string : spans → string
spans-to-string (regular-spans ss) = "{\"spans\":[" ^ (string-concat-sep-map "," span-to-string ss) ^ "]}\n"
spans-to-string (global-error e o) = global-error-string (e ^ helper o)
  where helper : maybe span → string
        helper (just x) = ", \"global-error\":" ^ span-to-string x
        helper nothing = ""

add-span : span → spans → spans
add-span s (regular-spans ss) = regular-spans (s :: ss)
add-span s (global-error e e') = global-error e e'

put-spans : spans → IO ⊤
put-spans ss = putStr (spans-to-string ss)

--------------------------------------------------
-- spanM, a state monad for spans
--------------------------------------------------
spanM : Set → Set
spanM A = ctxt → spans → A × ctxt × spans

-- return for the spanM monad
spanMr : ∀{A : Set} → A → spanM A
spanMr a Γ ss = a , Γ , ss

spanMok : spanM ⊤
spanMok = spanMr triv

get-ctxt : ∀{A : Set} → (ctxt → spanM A) → spanM A
get-ctxt m Γ ss = m Γ Γ ss

set-ctxt : ctxt → spanM ⊤
set-ctxt Γ _ ss = triv , Γ , ss

infixl 2 _≫span_ _≫=span_ _≫=spanj_ _≫=spanm_

_≫=span_ : ∀{A B : Set} → spanM A → (A → spanM B) → spanM B
(m ≫=span m') ss Γ with m ss Γ
(m ≫=span m') _ _ | v , Γ , ss = m' v Γ ss

_≫span_ : ∀{A : Set} → spanM ⊤ → spanM A → spanM A
(m ≫span m') Γ ss with m Γ ss
(m ≫span m') _ _ | _ , Γ , ss = m' Γ ss

_≫=spanj_ : ∀{A : Set} → spanM (maybe A) → (A → spanM ⊤) → spanM ⊤
_≫=spanj_{A} m m' = m ≫=span cont
  where cont : maybe A → spanM ⊤
        cont nothing = spanMok
        cont (just x) = m' x

-- discard changes made by the first computation
_≫=spand_ : ∀{A B : Set} → spanM A → (A → spanM B) → spanM B
_≫=spand_{A} m m' Γ ss with m Γ ss 
_≫=spand_{A} m m' Γ ss | v , _ , _ = m' v Γ ss

_≫=spanm_ : ∀{A : Set} → spanM (maybe A) → (A → spanM (maybe A)) → spanM (maybe A)
_≫=spanm_{A} m m' = m ≫=span cont
  where cont : maybe A → spanM (maybe A)
        cont nothing = spanMr nothing
        cont (just a) = m' a

spanM-add : span → spanM ⊤
spanM-add s Γ ss = triv , Γ , add-span s ss

spanM-addl : 𝕃 span → spanM ⊤
spanM-addl [] = spanMok
spanM-addl (s :: ss) = spanM-add s ≫span spanM-addl ss

debug-span : posinfo → posinfo → 𝕃 tagged-val → span
debug-span pi pi' tvs = mk-span "Debug" pi pi' tvs

spanM-debug : posinfo → posinfo → 𝕃 tagged-val → spanM ⊤
--spanM-debug pi pi' tvs = spanM-add (debug-span pi pi' tvs)
spanM-debug pi pi' tvs = spanMok

--------------------------------------------------
-- tagged-val constants
--------------------------------------------------

explain : string → tagged-val
explain s = "explanation" , s

reason : string → tagged-val
reason s = "reason" , s

expected-type : type → tagged-val
expected-type tp = "expected-type" , to-string tp

missing-expected-type : tagged-val
missing-expected-type = "expected-type" , "[missing]"

hnf-type : ctxt → type → tagged-val
hnf-type Γ tp = "hnf of type" , to-string (hnf-term-type Γ tp)

hnf-expected-type : ctxt → type → tagged-val
hnf-expected-type Γ tp = "hnf of expected type" , to-string (hnf-term-type Γ tp)

expected-kind : kind → tagged-val
expected-kind tp = "expected kind" , to-string tp

expected-kind-if : maybe kind → 𝕃 tagged-val → 𝕃 tagged-val
expected-kind-if nothing tvs = tvs
expected-kind-if (just k) tvs = expected-kind k :: tvs

expected-type-if : maybe type → 𝕃 tagged-val → 𝕃 tagged-val
expected-type-if nothing tvs = tvs
expected-type-if (just tp) tvs = expected-type tp :: tvs

hnf-expected-type-if : ctxt → maybe type → 𝕃 tagged-val → 𝕃 tagged-val
hnf-expected-type-if Γ nothing tvs = tvs
hnf-expected-type-if Γ (just tp) tvs = hnf-expected-type Γ tp :: tvs

type-data : type → tagged-val
type-data tp = "type" , to-string tp 

missing-type : tagged-val
missing-type = "type" , "[undeclared]"

error-data : string → tagged-val
error-data s = "error" , s

warning-data : string → tagged-val
warning-data s = "warning" , s

check-for-type-mismatch : ctxt → string → type → type → 𝕃 tagged-val
check-for-type-mismatch Γ s tp tp' =
  expected-type tp :: [ type-data tp' ] ++
    (if conv-type Γ tp tp' then [] else [ error-data ("The expected type does not match the " ^ s ^ " type.") ])

check-for-type-mismatch-if : ctxt → string → maybe type → type → 𝕃 tagged-val
check-for-type-mismatch-if Γ s (just tp) tp' = check-for-type-mismatch Γ s tp tp'
check-for-type-mismatch-if Γ s nothing tp' = [ type-data tp' ]

summary-data : string → string → tagged-val
summary-data name classifier = "summary" , (name ^ " : " ^ classifier)

missing-kind : tagged-val
missing-kind = "kind" , "[undeclared]"

head-kind : kind → tagged-val
head-kind k = "the kind of the head" , to-string k

head-type : type → tagged-val
head-type t = "the type of the head" , to-string t

type-app-head : type → tagged-val
type-app-head tp = "the head" , to-string tp

term-app-head : term → tagged-val
term-app-head t = "the head" , to-string t

term-argument : term → tagged-val
term-argument t = "the argument" , to-string t

type-argument : type → tagged-val
type-argument t = "the argument" , to-string t

kind-data : kind → tagged-val
kind-data k = "kind" , to-string k

liftingType-data : liftingType → tagged-val
liftingType-data l = "lifting type" , liftingType-to-string l

kind-data-if : maybe kind → 𝕃 tagged-val
kind-data-if (just k) = [ kind-data k ]
kind-data-if nothing = []

super-kind-data : tagged-val
super-kind-data = "superkind" , "□"

symbol-data : string → tagged-val
symbol-data x = "symbol" , x

tk-data : tk → tagged-val
tk-data (Tkk k) = kind-data k
tk-data (Tkt t) = type-data t

location-data : location → tagged-val
location-data (file-name , pi) = "location" , (file-name ^ " - " ^ pi)

var-location-data : ctxt → var → tagged-val
var-location-data Γ x = location-data (ctxt-var-location Γ x)

checking-data : checking-mode → tagged-val
checking-data checking = "checking-mode" , "checking"
checking-data synthesizing = "checking-mode" , "synthesizing"
checking-data untyped = "checking-mode" , "untyped"

ll-data : language-level → tagged-val
ll-data x = "language-level" , ll-to-string x

ll-data-term = ll-data ll-term
ll-data-type = ll-data ll-type
ll-data-kind = ll-data ll-kind

binder-data : ℕ → tagged-val
binder-data n = "binder" , ℕ-to-string n

-- this is the subterm position in the parse tree (as determined by
-- spans) for the bound variable of a binder
binder-data-const : tagged-val
binder-data-const = binder-data 0

punctuation-data : tagged-val
punctuation-data = "punctuation" , "true"

not-for-navigation : tagged-val
not-for-navigation = "not-for-navigation" , "true"

keywords-data : type → tagged-val
keywords-data t =
  "keywords" , 
    (if is-equation t then
      "equation"
    else "")
    ^ " " ^
    (if is-equational t then
      "equational"
     else "")
keywords-data-kind : kind → tagged-val
keywords-data-kind k = 
  "keywords"  ,
    (if is-equational-kind k then "equational" else "")

--------------------------------------------------
-- span-creating functions
--------------------------------------------------

Rec-span : posinfo → posinfo → kind → span
Rec-span pi pi' k = mk-span "Recursive datatype definition" pi pi' 
                      (kind-data k
                    :: [])

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

TpVar-span : ctxt → posinfo → string → checking-mode → 𝕃 tagged-val → span
TpVar-span Γ pi v check tvs = mk-span "Type variable" pi (posinfo-plus-str pi v) (checking-data check :: ll-data-type :: var-location-data Γ v :: symbol-data v :: tvs)

Var-span : ctxt → posinfo → string → checking-mode → 𝕃 tagged-val → span
Var-span Γ pi v check tvs = mk-span "Term variable" pi (posinfo-plus-str pi v) (checking-data check :: ll-data-term :: var-location-data Γ v :: symbol-data v :: tvs)

KndVar-span : ctxt → posinfo → string → checking-mode → span
KndVar-span Γ pi v check = mk-span "Kind variable" pi (posinfo-plus-str pi v)
                       (checking-data check :: ll-data-kind :: var-location-data Γ v :: symbol-data v :: [ super-kind-data ])

var-span : ctxt → posinfo → string → checking-mode → tk → span
var-span Γ pi x check (Tkk k) = TpVar-span Γ pi x check (keywords-data-kind k :: [ kind-data k ])
var-span Γ pi x check (Tkt t) = Var-span Γ pi x check (keywords-data t :: type-data t :: [ hnf-type Γ t ])

TpAppt-span : type → term → checking-mode → 𝕃 tagged-val → span
TpAppt-span tp t check tvs = mk-span "Application of a type to a term" (type-start-pos tp) (term-end-pos t) (checking-data check :: ll-data-type :: tvs)

TpApp-span : type → type → checking-mode → 𝕃 tagged-val → span
TpApp-span tp tp' check tvs = mk-span "Application of a type to a type" (type-start-pos tp) (type-end-pos tp') (checking-data check :: ll-data-type :: tvs)

App-span : term → term → checking-mode → 𝕃 tagged-val → span
App-span t t' check tvs = mk-span "Application of a term to a term" (term-start-pos t) (term-end-pos t') (checking-data check :: ll-data-term :: tvs)

AppTp-span : term → type → checking-mode → 𝕃 tagged-val → span
AppTp-span t tp check tvs = mk-span "Application of a term to a type" (term-start-pos t) (type-end-pos tp) (checking-data check :: ll-data-term :: tvs)

TpQuant-e = 𝔹

is-pi : TpQuant-e
is-pi = tt

TpQuant-span : TpQuant-e → posinfo → var → tk → type → checking-mode → 𝕃 tagged-val → span
TpQuant-span is-pi pi x atk body check tvs =
  mk-span (if is-pi then "Dependent function type" else "Implicit dependent function type")
       pi (type-end-pos body) (checking-data check :: ll-data-type :: binder-data-const :: tvs)

TpLambda-span : posinfo → var → tk → type → checking-mode → 𝕃 tagged-val → span
TpLambda-span pi x atk body check tvs =
  mk-span "Type-level lambda abstraction" pi (type-end-pos body)
    (checking-data check :: ll-data-type :: binder-data-const :: tvs)

Iota-span : posinfo → type → 𝕃 tagged-val → span
Iota-span pi t2 tvs = mk-span "Iota-abstraction" pi (type-end-pos t2) (explain "A dependent intersection type" :: tvs)

-- a span boxing up the parameters and the indices of a Rec definition
RecPrelim-span : string → posinfo → posinfo → span
RecPrelim-span name pi pi' = mk-span ("Parameters, indices, and constructor declarations for datatype " ^ name) pi pi' []

TpArrow-span : type → type → checking-mode → 𝕃 tagged-val → span
TpArrow-span t1 t2 check tvs = mk-span "Arrow type" (type-start-pos t1) (type-end-pos t2) (checking-data check :: ll-data-type :: tvs)

TpEq-span : term → term → checking-mode → 𝕃 tagged-val → span
TpEq-span t1 t2 check tvs = mk-span "Equation" (term-start-pos t1) (term-end-pos t2) (checking-data check :: ll-data-type :: tvs)

Star-span : posinfo → checking-mode → span
Star-span pi check = mk-span Star-name pi (posinfo-plus pi 1) (checking-data check :: [ ll-data-kind ])

KndPi-span : posinfo → var → tk → kind → checking-mode → span
KndPi-span pi x atk k check =
  mk-span "Pi kind" pi (kind-end-pos k)
    (checking-data check :: ll-data-kind :: binder-data-const :: [ super-kind-data ])

KndArrow-span : kind → kind → checking-mode → span
KndArrow-span k k' check = mk-span "Arrow kind" (kind-start-pos k) (kind-end-pos k') (checking-data check :: ll-data-kind :: [ super-kind-data ])

KndTpArrow-span : type → kind → checking-mode → span
KndTpArrow-span t k check = mk-span "Arrow kind" (type-start-pos t) (kind-end-pos k) (checking-data check :: ll-data-kind :: [ super-kind-data ])

rectype-name-span : posinfo → var → type → kind → checking-mode → span
rectype-name-span pi v tp k check =
  mk-span "Recursively defined type" pi (posinfo-plus-str pi v)
    (checking-data check :: summary-data v (to-string k) :: [ "definition" , to-string tp ])

Udefse-span : posinfo → 𝕃 tagged-val → span
Udefse-span pi tvs = mk-span "Empty constructor definitions part of a recursive type definition" pi (posinfo-plus pi 1) tvs

Ctordeclse-span : posinfo → 𝕃 tagged-val → span
Ctordeclse-span pi tvs = mk-span "Empty constructor declarations part of a recursive type definition" pi (posinfo-plus pi 1) tvs

erasure : term → tagged-val
erasure t = "erasure" , to-string (erase-term t)

Udef-span : posinfo → var → posinfo → term → 𝕃 tagged-val → span
Udef-span pi x pi' t tvs =
  let tvs = tvs ++ ( explain ("Definition of constructor " ^ x) :: [ erasure t ]) in
    mk-span "Constructor definition" pi pi' tvs

Ctordecl-span : posinfo → var → type → 𝕃 tagged-val → span
Ctordecl-span pi x tp tvs =
  mk-span "Constructor declaration" pi (type-end-pos tp)
    (summary-data ("ctor " ^ x) (to-string tp) :: tvs ++ [ explain ("Declaration of a type for constructor " ^ x)])

Udefs-span : udefs → span
Udefs-span us = mk-span "Constructor definitions (using lambda encodings)" (udefs-start-pos us) (udefs-end-pos us) []

Lam-span-erased : lam → string
Lam-span-erased ErasedLambda = "Erased lambda abstraction (term-level)"
Lam-span-erased KeptLambda = "Lambda abstraction (term-level)"

Lam-span : posinfo → lam → var → optClass → term → 𝕃 tagged-val → span
Lam-span pi l x NoClass tp tvs = mk-span (Lam-span-erased l) pi (term-end-pos tp) (ll-data-term :: binder-data-const :: tvs)
Lam-span pi l x (SomeClass atk) tp tvs = mk-span (Lam-span-erased l) pi (term-end-pos tp) 
                                           ((ll-data-term :: binder-data-const :: tvs)
                                           ++ [ "type of bound variable" , tk-to-string atk ])

DefTerm-span : posinfo → var → (checked : checking-mode) → maybe type → term → posinfo → 𝕃 tagged-val → span
DefTerm-span pi x checked tp t pi' tvs = 
  h ((h-summary tp) ++ (erasure t :: tvs)) pi x checked tp pi'
  where h : 𝕃 tagged-val → posinfo → var → (checked : checking-mode) → maybe type → posinfo → span
        h tvs pi x checking _ pi' = 
          mk-span "Term-level definition (checking)" pi pi'  tvs
        h tvs pi x _ (just tp) pi' = 
          mk-span "Term-level definition (synthesizing)" pi pi' (("synthesized type" , to-string tp) :: tvs)
        h tvs pi x _ nothing pi' = 
          mk-span "Term-level definition (synthesizing)" pi pi' (("synthesized type" , "[nothing]") :: tvs)
        h-summary : maybe type → 𝕃 tagged-val
        h-summary nothing = [(checking-data synthesizing)]
        h-summary (just tp) = (checking-data checking :: [ summary-data x (to-string tp) ])
    
CheckTerm-span : (checked : checking-mode) → maybe type → term → posinfo → 𝕃 tagged-val → span
CheckTerm-span checked tp t pi' tvs = 
  h (erasure t :: tvs) checked tp (term-start-pos t) pi'
  where h : 𝕃 tagged-val → (checked : checking-mode) → maybe type → posinfo → posinfo → span
        h tvs checking _ pi pi' = 
          mk-span "Checking a term" pi pi' (checking-data checking :: tvs)
        h tvs _ (just tp) pi pi' = 
          mk-span "Synthesizing a type for a term" pi pi' (checking-data synthesizing :: ("synthesized type" , to-string tp) :: tvs)
        h tvs _ nothing pi pi' = 
          mk-span "Synthesizing a type for a term" pi pi' (checking-data synthesizing :: ("synthesized type" , "[nothing]") :: tvs)

normalized-type : type → tagged-val
normalized-type tp = "normalized type" , to-string tp

DefType-span : posinfo → var → (checked : checking-mode) → maybe kind → type → posinfo → 𝕃 tagged-val → span
DefType-span pi x checked mk tp pi' tvs =
  h ((h-summary mk) ++ tvs) checked mk
  where h : 𝕃 tagged-val → checking-mode → maybe kind → span
        h tvs checking _ = mk-span "Type-level definition (checking)" pi pi' tvs
        h tvs _ (just k) =
          mk-span "Type-level definition (synthesizing)" pi pi' ( ("synthesized kind" , to-string k) :: tvs)
        h tvs _ nothing =
          mk-span "Type-level definition (synthesizing)" pi pi' ( ("synthesized kind" , "[nothing]") :: tvs)
        h-summary : maybe kind → 𝕃 tagged-val
        h-summary nothing = [(checking-data synthesizing)]
        h-summary (just k) = (checking-data checking :: [ summary-data x (to-string k) ])

DefKind-span : posinfo → var → kind → posinfo → span
DefKind-span pi x k pi' = mk-span "Kind-level definition" pi pi' [ summary-data x "□" ]

unimplemented-term-span : posinfo → posinfo → maybe type → span
unimplemented-term-span pi pi' nothing = mk-span "Unimplemented" pi pi' [ error-data "Unimplemented synthesizing a type for a term" ]
unimplemented-term-span pi pi' (just tp) = mk-span "Unimplemented" pi pi' 
                                              ( error-data "Unimplemented checking a term against a type" ::
                                                ll-data-term :: [ expected-type tp ])

unchecked-term-span : term → span
unchecked-term-span t = mk-span "Unchecked term" (term-start-pos t) (term-end-pos t)
                           (ll-data-term :: not-for-navigation :: [ explain "This term has not been type-checked."])

unimplemented-type-span : posinfo → posinfo → maybe kind → span
unimplemented-type-span pi pi' nothing = mk-span "Unimplemented" pi pi' (checking-data synthesizing :: error-data "Unimplemented synthesizing a kind for a type" :: [] )
unimplemented-type-span pi pi' (just k) = mk-span "Unimplemented" pi pi' 
                                              ( error-data "Unimplemented checking a type against a kind" ::
                                                checking-data checking :: ll-data-type :: [ expected-kind k ])

Beta-span : posinfo → checking-mode → 𝕃 tagged-val → span
Beta-span pi check  tvs = mk-span "Beta axiom" pi (posinfo-plus pi 1) 
                     (checking-data check :: ll-data-term :: explain "A term constant whose type states that β-equal terms are provably equal" :: tvs)

Delta-span : posinfo → term → checking-mode → 𝕃 tagged-val → span
Delta-span pi t check tvs = mk-span "Delta" pi (term-end-pos t) 
                       (checking-data check :: ll-data-term :: tvs ++
                        [ explain ("A term for proving any formula one wishes, given a proof of a beta-equivalence which is "
                                  ^ "false.")])

PiInj-span : posinfo → num → term → checking-mode → 𝕃 tagged-val → span
PiInj-span pi n t check tvs = mk-span "Pi proof" pi (term-end-pos t) 
                          (checking-data check :: ll-data-term :: tvs ++
                               [ explain ("A term for deducing that the argument in position " ^ n ^ " of a head-normal form on "
                                           ^ "the lhs of the equation proved by the subterm is equal to the corresponding argument " 
                                           ^ "of the rhs") ])

hole-span : ctxt → posinfo → maybe type → 𝕃 tagged-val → span
hole-span Γ pi tp tvs = 
  mk-span "Hole" pi (posinfo-plus pi 1) 
    (ll-data-term :: error-data "This hole remains to be filled in" :: expected-type-if tp (hnf-expected-type-if Γ tp tvs))

expected-to-string : checking-mode → string
expected-to-string checking = "expected"
expected-to-string synthesizing = "synthesized"
expected-to-string untyped = "untyped"

Epsilon-span : posinfo → leftRight → maybeMinus → term → checking-mode → 𝕃 tagged-val → span
Epsilon-span pi lr m t check tvs = mk-span "Epsilon" pi (term-end-pos t) 
                                         (checking-data check :: ll-data-term :: tvs ++
                                         [ explain ("Normalize " ^ side lr ^ " of the " 
                                                   ^ expected-to-string check ^ " equation, using " ^ maybeMinus-description m 
                                                   ^ " reduction." ) ])
  where side : leftRight → string
        side Left = "the left-hand side"
        side Right = "the right-hand side"
        side Both = "both sides"
        maybeMinus-description : maybeMinus → string
        maybeMinus-description EpsHnf = "head"
        maybeMinus-description EpsHanf = "head-applicative"

Rho-span : posinfo → term → term → checking-mode → rho → ℕ → 𝕃 tagged-val → span
Rho-span pi t t' expected r numrewrites tvs = mk-span "Rho" pi (term-end-pos t') 
                                  (checking-data expected :: ll-data-term :: tvs ++
                                    ((if (numrewrites =ℕ 0) then (error-data "No rewrites could be performed.")
                                     else ("Number of rewrites", ℕ-to-string numrewrites)) ::
                                     [ explain ("Rewrite terms in the " 
                                             ^ expected-to-string expected ^ " type, using an equation. "
                                             ^ (if (is-rho-plus r) then "" else "Do not ") ^ "Beta-reduce the type as we look for matches.") ]))

Chi-span : posinfo → maybeAtype → term → checking-mode → 𝕃 tagged-val → span
Chi-span pi m t' check tvs = mk-span "Chi" pi (term-end-pos t')  (ll-data-term :: checking-data check :: tvs ++ helper m)
  where helper : maybeAtype → 𝕃 tagged-val
        helper (Atype T) =  explain ("Check a term against an asserted type") :: [ "the asserted type " , to-string T ]
        helper NoAtype = [ explain ("Change from checking mode (outside the term) to synthesizing (inside)") ] 

Sigma-span : posinfo → term → maybe type → 𝕃 tagged-val → span
Sigma-span pi t expected tvs =
  mk-span "Sigma" pi (term-end-pos t) 
     (ll-data-term :: checking-data (maybe-to-checking expected) :: tvs ++
     (explain ("Swap the sides of the equation synthesized for the body of this term.")
     :: expected-type-if expected []))

motive-label : string
motive-label = "the motive"

the-motive : type → tagged-val
the-motive motive = motive-label , to-string motive

Theta-span : posinfo → theta → term → lterms → checking-mode → 𝕃 tagged-val → span
Theta-span pi u t ls check tvs = mk-span "Theta" pi (lterms-end-pos ls) (ll-data-term :: checking-data check :: tvs ++ do-explain u)
  where do-explain : theta → 𝕃 tagged-val
        do-explain Abstract = [ explain ("Perform an elimination with the first term, after abstracting it from the expected type.") ]
        do-explain (AbstractVars vs) = [ explain ("Perform an elimination with the first term, after abstracting the listed variables (" 
                                               ^ vars-to-string vs ^ ") from the expected type.") ]
        do-explain AbstractEq = [ explain ("Perform an elimination with the first term, after abstracting it with an equation " 
                                         ^ "from the expected type.") ]


normalized-term-if : ctxt → cmdTerminator → term → 𝕃 tagged-val
normalized-term-if Γ Normalize e = [ "normalized term" , to-string (hnf Γ unfold-all e) ]
normalized-term-if Γ Hnf e = [ "hnf term" , to-string (hnf Γ unfold-head e) ]
normalized-term-if Γ Hanf e = [ "hanf term" , to-string (hanf Γ e) ]
normalized-term-if Γ EraseOnly e = []

normalized-type-if : ctxt → cmdTerminator → type → 𝕃 tagged-val
normalized-type-if Γ Normalize e = [ "normalized type" , to-string (hnf Γ unfold-all e) ]
normalized-type-if Γ EraseOnly e = []
normalized-type-if Γ _ {- Hnf or Hanf -} e = [ "hnf type" , to-string (hnf Γ unfold-head e) ]

Lft-span : posinfo → var → term → checking-mode → 𝕃 tagged-val → span
Lft-span pi X t check tvs = mk-span "Lift type" pi (term-end-pos t) (checking-data check :: ll-data-type :: binder-data-const :: tvs)

File-span : posinfo → posinfo → string → span
File-span pi pi' filename = mk-span ("Cedille source file (" ^ filename ^ ")") pi pi' []

Import-span : posinfo → string → posinfo → 𝕃 tagged-val → span
Import-span pi file pi' tvs = mk-span ("Import of another source file") pi pi' (location-data (file , first-position) :: tvs)

punctuation-span : string → posinfo → posinfo → span
punctuation-span name pi pi'  = mk-span name pi pi' ( punctuation-data ::  not-for-navigation :: [] )

whitespace-span : posinfo → posinfo → span
whitespace-span pi pi'  = mk-span "Whitespace" pi pi' [ not-for-navigation ]

comment-span : posinfo → posinfo → span
comment-span pi pi'  = mk-span "Comment" pi pi' [ not-for-navigation ]

InlineDef-span : posinfo → posinfo → var → term → posinfo → checking-mode → 𝕃 tagged-val → span
InlineDef-span pi pi' x t pi'' check tvs =
  mk-span "Inline definition" pi pi''
    (checking-data check :: warning-data "Currently the defined symbol cannot be used elsewhere (this will be changed soon)." :: 
    ll-data-term ::
    explain ("This definition of " ^ x ^ " is in scope to the end of the nearest enclosing binder.") :: tvs)

IotaPair-span : posinfo → posinfo → 𝕃 tagged-val → span
IotaPair-span pi pi' tvs = mk-span "Iota pair" pi pi' (explain "Inhabit a iota-type (dependent intersection type)." :: tvs)

IotaProj-span : term → posinfo → 𝕃 tagged-val → span
IotaProj-span t pi' tvs = mk-span "Iota projection" (term-start-pos t) pi' tvs
