module spans where

open import lib
open import cedille-types 
open import conversion
open import ctxt
open import is-free
open import general-util
open import syntax-util
open import to-string
open import subst


--------------------------------------------------
-- span datatype
--
-- individual spans with an error message should
-- include a tagged-val with the tag "error"
-- (see is-error-span below)
--------------------------------------------------
data span : Set where
  mk-span : string → posinfo → posinfo → 𝕃 tagged-val {- extra information for the span -} → span

span-to-streeng : span → streeng
span-to-streeng (mk-span name start end extra) = 
  [[ "[\"" ^ name ^ "\"," ^ start ^ "," ^ end ^ ",{" ]] ⊹⊹ tagged-vals-to-streeng 0 extra ⊹⊹ [[ "}]" ]]

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
global-error-string msg = "{\"error\":\"" ^ msg ^ "\"" ^ "}"

{-
spans-to-string : spans → string
spans-to-string (regular-spans ss) = "{\"spans\":[" ^ (string-concat-sep-map "," span-to-streeng ss) ^ "]}"
spans-to-string (global-error e o) = global-error-string (e ^ helper o)
  where helper : maybe span → string
        helper (just x) = ", \"global-error\":" ^ span-to-streeng x
        helper nothing = ""
-}

𝕃span-to-streeng : 𝕃 span → streeng
𝕃span-to-streeng (s :: []) = span-to-streeng s
𝕃span-to-streeng (s :: ss) = span-to-streeng s ⊹⊹ [[ "," ]] ⊹⊹ 𝕃span-to-streeng ss
𝕃span-to-streeng [] = [[]]

spans-to-streeng : spans → streeng
spans-to-streeng (regular-spans ss) = [[ "{\"spans\":["]] ⊹⊹ 𝕃span-to-streeng ss ⊹⊹ [[ "]}" ]] where
spans-to-streeng (global-error e s) =
  [[ global-error-string e ]] ⊹⊹ maybe-else [[]] (λ s → [[", \"global-error\":"]] ⊹⊹ span-to-streeng s) s

add-span : span → spans → spans
add-span s (regular-spans ss) = regular-spans (s :: ss)
add-span s (global-error e e') = global-error e e'

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

restore-def : Set
restore-def = maybe qualif-info × maybe sym-info

-- this returns the previous ctxt-info, if any, for the given variable
spanM-push-term-decl : posinfo → defScope → var → type → spanM restore-def
spanM-push-term-decl pi s x t Γ ss = let qi = ctxt-get-qi Γ x in (qi , ctxt-get-info (qi-var-if qi x) Γ) , ctxt-term-decl pi s x t Γ , ss

spanM-set-params : params → spanM ⊤
spanM-set-params ps Γ ss = triv , (ctxt-params-def ps Γ) , ss

spanM-push-term-def : posinfo → var → term → type → spanM restore-def
spanM-push-term-def pi x t T Γ ss = let qi = ctxt-get-qi Γ x in (qi , ctxt-get-info (qi-var-if qi x) Γ) , ctxt-term-def pi localScope x (hnf Γ unfold-head t tt) T Γ , ss

spanM-push-term-udef : posinfo → var → term → spanM restore-def
spanM-push-term-udef pi x t Γ ss = let qi = ctxt-get-qi Γ x in (qi , ctxt-get-info (qi-var-if qi x) Γ) , ctxt-term-udef pi localScope x t Γ , ss
 
 -- return previous ctxt-info, if any
spanM-push-type-decl : posinfo → defScope → var → kind → spanM restore-def
spanM-push-type-decl pi s x k Γ ss = let qi = ctxt-get-qi Γ x in (qi , ctxt-get-info (qi-var-if qi x) Γ) , ctxt-type-decl pi s x k Γ , ss
 
spanM-push-type-def : posinfo → var → type → kind → spanM restore-def
spanM-push-type-def pi x t T Γ ss = let qi = ctxt-get-qi Γ x in (qi , ctxt-get-info (qi-var-if qi x) Γ) , ctxt-type-def pi localScope x (hnf Γ unfold-head t tt) T Γ , ss

-- restore ctxt-info for the variable with given posinfo
spanM-restore-info : var → restore-def → spanM ⊤
spanM-restore-info v rd Γ ss = triv , ctxt-restore-info Γ v (fst rd) (snd rd) , ss

_≫span_ : ∀{A : Set} → spanM ⊤ → spanM A → spanM A
(m ≫span m') Γ ss with m Γ ss
(m ≫span m') _ _ | _ , Γ , ss = m' Γ ss

spanM-restore-info* : 𝕃 (var × restore-def) → spanM ⊤
spanM-restore-info* [] = spanMok
spanM-restore-info* ((v , qi , m) :: s) = spanM-restore-info v (qi , m) ≫span spanM-restore-info* s

set-ctxt : ctxt → spanM ⊤
set-ctxt Γ _ ss = triv , Γ , ss

infixl 2 _≫span_ _≫=span_ _≫=spanj_ _≫=spanm_ _≫=spanm'_

_≫=span_ : ∀{A B : Set} → spanM A → (A → spanM B) → spanM B
(m ≫=span m') ss Γ with m ss Γ
(m ≫=span m') _ _ | v , Γ , ss = m' v Γ ss

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

_≫=spanm'_ : ∀{A B : Set} → spanM (maybe A) → (A → spanM (maybe B)) → spanM (maybe B)
_≫=spanm'_{A}{B} m m' = m ≫=span cont
  where cont : maybe A → spanM (maybe B)
        cont nothing = spanMr nothing
        cont (just a) = m' a

_on-fail_≫=spanm'_ : ∀ {A B} → spanM (maybe A) → spanM B
                            → (A → spanM B) → spanM B
_on-fail_≫=spanm'_ {A}{B} m fail f = m ≫=span cont
  where cont : maybe A → spanM B
        cont nothing  = fail
        cont (just x) = f x

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

to-string-tag-tk : (tag : string) → ctxt → tk → tagged-val
to-string-tag-tk t Γ (Tkt T) = to-string-tag t Γ T
to-string-tag-tk t Γ (Tkk k) = to-string-tag t Γ k


--------------------------------------------------
-- tagged-val constants
--------------------------------------------------

location-data : location → tagged-val
location-data (file-name , pi) = "location" , [[ file-name ]] ⊹⊹ [[ " - " ]] ⊹⊹ [[ pi ]] , []

{-# TERMINATING #-}
var-location-data : ctxt → var → maybe language-level → tagged-val
var-location-data Γ x (just ll-term) with ctxt-var-location Γ x | qualif-term Γ (Var posinfo-gen x)
...| ("missing" , "missing") | (Var pi x') = location-data (ctxt-var-location Γ x')
...| loc | _ = location-data loc
var-location-data Γ x (just ll-type) with ctxt-var-location Γ x | qualif-type Γ (TpVar posinfo-gen x)
...| ("missing" , "missing") | (TpVar pi x') = location-data (ctxt-var-location Γ x')
...| loc | _ = location-data loc
var-location-data Γ x (just ll-kind) with ctxt-var-location Γ x | qualif-kind Γ (KndVar posinfo-gen x (ArgsNil posinfo-gen))
...| ("missing" , "missing") | (KndVar pi x' as) = location-data (ctxt-var-location Γ x')
...| loc | _ = location-data loc
var-location-data Γ x nothing with ctxt-lookup-term-var Γ x | ctxt-lookup-type-var Γ x | ctxt-lookup-kind-var-def Γ x
...| just _ | _ | _ = var-location-data Γ x (just ll-term)
...| _ | just _ | _ = var-location-data Γ x (just ll-type)
...| _ | _ | just _ = var-location-data Γ x (just ll-kind)
...| _ | _ | _ = location-data ("missing" , "missing")

explain : string → tagged-val
explain s = "explanation" , [[ s ]] , []

reason : string → tagged-val
reason s = "reason" , [[ s ]] , []

expected-type : ctxt → type → tagged-val
expected-type = to-string-tag "expected-type"

missing-expected-type : tagged-val
missing-expected-type = "expected-type" , [[ "[missing]" ]] , []

hnf-type : ctxt → type → tagged-val
hnf-type Γ tp = to-string-tag "hnf of type" Γ (hnf-term-type Γ tp)

hnf-expected-type : ctxt → type → tagged-val
hnf-expected-type Γ tp = to-string-tag "hnf of expected type" Γ (hnf-term-type Γ tp)

expected-kind : ctxt → kind → tagged-val
expected-kind = to-string-tag "expected kind"

expected-kind-if : ctxt → maybe kind → 𝕃 tagged-val
expected-kind-if _ nothing = []
expected-kind-if Γ (just k) = [ expected-kind Γ k ]

expected-type-if : ctxt → maybe type → 𝕃 tagged-val
expected-type-if _ nothing = []
expected-type-if Γ (just tp) = [ expected-type Γ tp ]

hnf-expected-type-if : ctxt → maybe type → 𝕃 tagged-val
hnf-expected-type-if Γ nothing = []
hnf-expected-type-if Γ (just tp) = [ hnf-expected-type Γ tp ]

type-data : ctxt → type → tagged-val
type-data = to-string-tag "type"

missing-type : tagged-val
missing-type = "type" , [[ "[undeclared]" ]] , []

error-data : string → tagged-val
error-data s = "error" , [[ s ]] , []

warning-data : string → tagged-val
warning-data s = "warning" , [[ s ]] , []

check-for-type-mismatch : ctxt → string → type → type → 𝕃 tagged-val
check-for-type-mismatch Γ s tp tp' = let tp'' = hnf Γ unfold-head tp' tt in
  expected-type Γ tp :: type-data Γ tp'' ::
    (if conv-type Γ tp tp'' then [] else
      [ error-data ("The expected type does not match the " ^ s ^ " type.") ])

check-for-type-mismatch-if : ctxt → string → maybe type → type → 𝕃 tagged-val
check-for-type-mismatch-if Γ s (just tp) = check-for-type-mismatch Γ s tp
check-for-type-mismatch-if Γ s nothing tp = [ type-data Γ tp ]

summary-data : {ed : exprd} → (pi : string) → (fn : string) → (pos : posinfo) → ctxt → ⟦ ed ⟧ → tagged-val
summary-data name fn pi Γ t with (strVar name ≫str strAdd " : " ≫str to-stringh' neither t) {TERM} [[]] 0 [] Γ nothing neither
...| (s , n , ts') = "summary" , s , ts'

missing-kind : tagged-val
missing-kind = "kind" , [[ "[undeclared]" ]] , []

head-kind : ctxt → kind → tagged-val
head-kind = to-string-tag "the kind of the head"

head-type : ctxt → type → tagged-val
head-type = to-string-tag "the type of the head"

arg-type : ctxt → type → tagged-val
arg-type = to-string-tag "the type of the arg"

type-app-head : ctxt → type → tagged-val
type-app-head = to-string-tag "the head"

term-app-head : ctxt → term → tagged-val
term-app-head = to-string-tag "the head"

term-argument : ctxt → term → tagged-val
term-argument = to-string-tag "the argument"

type-argument : ctxt → type → tagged-val
type-argument = to-string-tag "the argument"

arg-argument : ctxt → arg → tagged-val
arg-argument Γ (TermArg x) = term-argument Γ x
arg-argument Γ (TypeArg x) = type-argument Γ x

kind-data : ctxt → kind → tagged-val
kind-data = to-string-tag "kind"

liftingType-data : ctxt → liftingType → tagged-val
liftingType-data = to-string-tag "lifting type"

kind-data-if : ctxt → maybe kind → 𝕃 tagged-val
kind-data-if Γ (just k) = [ kind-data Γ k ]
kind-data-if _ nothing = []

super-kind-data : tagged-val
super-kind-data = "superkind" , [[ "□" ]] , []

symbol-data : string → tagged-val
symbol-data x = "symbol" , [[ x ]] , []

tk-data : ctxt → tk → tagged-val
tk-data Γ (Tkk k) = kind-data Γ k
tk-data Γ (Tkt t) = type-data Γ t

checking-data : checking-mode → tagged-val
checking-data checking = "checking-mode" , [[ "checking" ]] , []
checking-data synthesizing = "checking-mode" , [[ "synthesizing" ]] , []
checking-data untyped = "checking-mode" , [[ "untyped" ]] , []

ll-data : language-level → tagged-val
ll-data x = "language-level" , [[ ll-to-string x ]] , []

ll-data-term = ll-data ll-term
ll-data-type = ll-data ll-type
ll-data-kind = ll-data ll-kind

binder-data : ℕ → tagged-val
binder-data n = "binder" , [[ ℕ-to-string n ]] , []

-- this is the subterm position in the parse tree (as determined by
-- spans) for the bound variable of a binder
binder-data-const : tagged-val
binder-data-const = binder-data 0

bound-data : defTermOrType → ctxt → tagged-val
bound-data (DefTerm pi v mtp t) Γ = to-string-tag "bound-value" Γ t
bound-data (DefType pi v k tp) Γ = to-string-tag "bound-value" Γ tp

punctuation-data : tagged-val
punctuation-data = "punctuation" , [[ "true" ]] , []

not-for-navigation : tagged-val
not-for-navigation = "not-for-navigation" , [[ "true" ]] , []

is-erased : type → 𝔹
is-erased (TpVar _ _ ) = tt
is-erased _ = ff

erased? = 𝔹

keywords-data : erased? → type → tagged-val
keywords-data e t =
  "keywords" , 
    (if is-equation t then
      [[ "equation" ]]
    else [[]])
    ⊹⊹ [[ " " ]] ⊹⊹
    (if is-equational t then
      [[ "equational" ]]
     else [[]])
    ⊹⊹ [[ if e then " erased" else " noterased" ]] , []




keywords-data-kind : kind → tagged-val
keywords-data-kind k = 
  "keywords"  ,
    (if is-equational-kind k then [[ "equational" ]] else [[]]) ⊹⊹ [[ " noterased" ]] , []



error-if-not-eq : ctxt → type → 𝕃 tagged-val → 𝕃 tagged-val
error-if-not-eq Γ (TpEq t1 t2) tvs = expected-type Γ (TpEq t1 t2) :: tvs
error-if-not-eq Γ tp tvs = error-data "This term is being checked against the following type, but an equality type was expected"
                     :: expected-type Γ tp :: tvs

error-if-not-eq-maybe : ctxt → maybe type → 𝕃 tagged-val → 𝕃 tagged-val
error-if-not-eq-maybe Γ (just tp) tvs = error-if-not-eq Γ tp tvs
error-if-not-eq-maybe _ _ tvs = tvs

--------------------------------------------------
-- span-creating functions
--------------------------------------------------

Rec-span : posinfo → posinfo → kind → span
Rec-span pi pi' k = mk-span "Recursive datatype definition" pi pi' 
                      (kind-data (new-ctxt "" "") k
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
                                      pi pi' [ binder-data-const ]

TpVar-span : ctxt → posinfo → string → checking-mode → 𝕃 tagged-val → span
TpVar-span Γ pi v check tvs = mk-span "Type variable" pi (posinfo-plus-str pi (unqual-local v)) (checking-data check :: ll-data-type :: var-location-data Γ v (just ll-type) :: symbol-data (unqual-local v) :: tvs)

Var-span : ctxt → posinfo → string → checking-mode → 𝕃 tagged-val → span
Var-span Γ pi v check tvs = mk-span "Term variable" pi (posinfo-plus-str pi (unqual-local v)) (checking-data check :: ll-data-term :: var-location-data Γ v (just ll-term) :: symbol-data (unqual-local v) :: tvs)

KndVar-span : ctxt → posinfo → string → args → checking-mode → 𝕃 tagged-val → span
KndVar-span Γ pi v ys check tvs =
  mk-span "Kind variable" pi (args-end-pos ys)
    (checking-data check :: ll-data-kind :: var-location-data Γ v (just ll-kind) :: symbol-data (unqual-local v) :: super-kind-data :: tvs)

var-span :  erased? → ctxt → posinfo → string → checking-mode → tk → span
var-span _ Γ pi x check (Tkk k) = TpVar-span Γ pi x check (keywords-data-kind k :: [ kind-data Γ k ])
var-span e Γ pi x check (Tkt t) = Var-span Γ pi x check (keywords-data e t :: type-data Γ t :: [ hnf-type Γ t ])



redefined-var-span : ctxt → posinfo → var → span
redefined-var-span Γ pi x = mk-span "Variable definition" pi (posinfo-plus-str pi x)
                             (error-data "This symbol was defined already." :: var-location-data Γ x nothing :: [])

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
Iota-span pi t2 tvs = mk-span "Iota-abstraction" pi (type-end-pos t2) (explain "A dependent intersection type" :: ll-data-type :: tvs)

TpArrow-span : type → type → checking-mode → 𝕃 tagged-val → span
TpArrow-span t1 t2 check tvs = mk-span "Arrow type" (type-start-pos t1) (type-end-pos t2) (checking-data check :: ll-data-type :: tvs)

TpEq-span : term → term → checking-mode → 𝕃 tagged-val → span
TpEq-span t1 t2 check tvs = mk-span "Equation" (term-start-pos t1) (term-end-pos t2)
                             (explain "Equation between terms" :: checking-data check :: ll-data-type :: tvs)

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

erasure : ctxt → term → tagged-val
erasure Γ t = to-string-tag "erasure" Γ (erase-term t)

Lam-span-erased : lam → string
Lam-span-erased ErasedLambda = "Erased lambda abstraction (term-level)"
Lam-span-erased KeptLambda = "Lambda abstraction (term-level)"

Lam-span : ctxt → checking-mode → posinfo → lam → var → optClass → term → 𝕃 tagged-val → span
Lam-span _ c pi l x NoClass t tvs = mk-span (Lam-span-erased l) pi (term-end-pos t) (ll-data-term :: binder-data-const :: checking-data c :: tvs)
Lam-span Γ c pi l x (SomeClass atk) t tvs = mk-span (Lam-span-erased l) pi (term-end-pos t) 
                                           ((ll-data-term :: binder-data-const :: checking-data c :: tvs)
                                           ++ [ to-string-tag-tk "type of bound variable" Γ atk ])


compileFail-in : ctxt → (original erased normalized : term) → 𝕃 tagged-val
compileFail-in Γ o e n with is-free-in-term check-erased compileFail
...| is-free with is-free o
...| ff = []
...| tt with is-free n | is-free e
...| tt | _ = error-data "compileFail occurs in the normalized term" :: [ to-string-tag "normalized term" Γ n ]
...| ff | ff = error-data "compileFail occurs in an erased position" :: [ to-string-tag "the term" Γ o ]
...| ff | tt = []


DefTerm-span : ctxt → posinfo → var → (checked : checking-mode) → maybe type → term → posinfo → 𝕃 tagged-val → span
DefTerm-span Γ pi x checked tp t pi' tvs = 
  h ((h-summary tp) ++ (erasure Γ t :: tvs)) pi x checked tp pi'
  where h : 𝕃 tagged-val → posinfo → var → (checked : checking-mode) → maybe type → posinfo → span
        h tvs pi x checking _ pi' = 
          mk-span "Term-level definition (checking)" pi pi'  tvs
        h tvs pi x _ (just tp) pi' = 
          mk-span "Term-level definition (synthesizing)" pi pi' (to-string-tag "synthesized type" Γ tp :: tvs)
        h tvs pi x _ nothing pi' = 
          mk-span "Term-level definition (synthesizing)" pi pi' (("synthesized type" , [[ "[nothing]" ]] , []) :: tvs)
        h-summary : maybe type → 𝕃 tagged-val
        h-summary nothing = [(checking-data synthesizing)]
        h-summary (just tp) = (checking-data checking :: [ summary-data x pi (ctxt-get-current-filename Γ) Γ tp ])
    
CheckTerm-span : ctxt → (checked : checking-mode) → maybe type → term → posinfo → 𝕃 tagged-val → span
CheckTerm-span Γ checked tp t pi' tvs = 
  h (erasure Γ t :: tvs) checked tp (term-start-pos t) pi'
  where h : 𝕃 tagged-val → (checked : checking-mode) → maybe type → posinfo → posinfo → span
        h tvs checking _ pi pi' = 
          mk-span "Checking a term" pi pi' (checking-data checking :: tvs)
        h tvs _ (just tp) pi pi' = 
          mk-span "Synthesizing a type for a term" pi pi' (checking-data synthesizing :: to-string-tag "synthesized type" Γ tp :: tvs)
        h tvs _ nothing pi pi' = 
          mk-span "Synthesizing a type for a term" pi pi' (checking-data synthesizing :: ("synthesized type" , [[ "[nothing]" ]] , []) :: tvs)

normalized-type : ctxt → type → tagged-val
normalized-type = to-string-tag "normalized type"

DefType-span : ctxt → posinfo → var → (checked : checking-mode) → maybe kind → type → posinfo → 𝕃 tagged-val → span
DefType-span Γ pi x checked mk tp pi' tvs =
  h ((h-summary mk) ++ tvs) checked mk
  where h : 𝕃 tagged-val → checking-mode → maybe kind → span
        h tvs checking _ = mk-span "Type-level definition (checking)" pi pi' tvs
        h tvs _ (just k) =
          mk-span "Type-level definition (synthesizing)" pi pi' (to-string-tag "synthesized kind" Γ k :: tvs)
        h tvs _ nothing =
          mk-span "Type-level definition (synthesizing)" pi pi' ( ("synthesized kind" , [[ "[nothing]" ]] , []) :: tvs)
        h-summary : maybe kind → 𝕃 tagged-val
        h-summary nothing = [(checking-data synthesizing)]
        h-summary (just k) = (checking-data checking :: [ summary-data x (ctxt-get-current-filename Γ) pi Γ k ])

DefKind-span : ctxt → posinfo → var → kind → posinfo → span
DefKind-span Γ pi x k pi' = mk-span "Kind-level definition" pi pi' (kind-data Γ k :: [ summary-data x (ctxt-get-current-filename Γ) pi Γ (Var pi "□") ])

unimplemented-term-span : ctxt → posinfo → posinfo → maybe type → span
unimplemented-term-span _ pi pi' nothing = mk-span "Unimplemented" pi pi' [ error-data "Unimplemented synthesizing a type for a term" ]
unimplemented-term-span Γ pi pi' (just tp) = mk-span "Unimplemented" pi pi' 
                                              ( error-data "Unimplemented checking a term against a type" ::
                                                ll-data-term :: [ expected-type Γ tp ])

unchecked-term-span : term → span
unchecked-term-span t = mk-span "Unchecked term" (term-start-pos t) (term-end-pos t)
                           (ll-data-term :: not-for-navigation :: [ explain "This term has not been type-checked."])

unimplemented-type-span : ctxt → posinfo → posinfo → maybe kind → span
unimplemented-type-span _ pi pi' nothing = mk-span "Unimplemented" pi pi' (checking-data synthesizing :: error-data "Unimplemented synthesizing a kind for a type" :: [] )
unimplemented-type-span Γ pi pi' (just k) = mk-span "Unimplemented" pi pi' 
                                              ( error-data "Unimplemented checking a type against a kind" ::
                                                checking-data checking :: ll-data-type :: [ expected-kind Γ k ])

Beta-span : posinfo → posinfo → checking-mode → 𝕃 tagged-val → span
Beta-span pi pi' check tvs = mk-span "Beta axiom" pi pi'
                     (checking-data check :: ll-data-term :: explain "A term constant whose type states that β-equal terms are provably equal" :: tvs)

Delta-span : posinfo → term → checking-mode → 𝕃 tagged-val → span
Delta-span pi t check tvs = mk-span "Delta" pi (term-end-pos t) 
                       (checking-data check :: ll-data-term :: tvs ++
                        [ explain ("A term for proving any formula one wishes, given a proof of a beta-equivalence which is "
                                  ^ "false.")])

Fold-span : posinfo → term → checking-mode → 𝕃 tagged-val → span
Fold-span pi t check tvs = mk-span "Fold" pi (term-end-pos t)
                       (checking-data check :: ll-data-term :: tvs ++
                       [ explain ("A primitive proving that a term that inhabits the unfolding of a recursive type"
                                  ^ "inhabits that recursive type.")])

Unfold-span : posinfo → term → checking-mode → 𝕃 tagged-val → span
Unfold-span pi t check tvs = mk-span "Unfold" pi (term-end-pos t)
                       (checking-data check :: ll-data-term :: tvs ++
                       [ explain ("A primitive proving that a term that inhabits a recursive type"
                                  ^ "inhabits the unfolding of that recursive type.")])

PiInj-span : posinfo → num → term → checking-mode → 𝕃 tagged-val → span
PiInj-span pi n t check tvs = mk-span "Pi proof" pi (term-end-pos t) 
                          (checking-data check :: ll-data-term :: tvs ++
                               [ explain ("A term for deducing that the argument in position " ^ n ^ " of a head-normal form on "
                                           ^ "the lhs of the equation proved by the subterm is equal to the corresponding argument " 
                                           ^ "of the rhs") ])

hole-span : ctxt → posinfo → maybe type → 𝕃 tagged-val → span
hole-span Γ pi tp tvs = 
  mk-span "Hole" pi (posinfo-plus pi 1)
    (ll-data-term :: error-data "This hole remains to be filled in" ::
     expected-type-if Γ tp ++ hnf-expected-type-if Γ tp ++ tvs)

tp-hole-span : ctxt → posinfo → maybe kind → 𝕃 tagged-val → span
tp-hole-span Γ pi k tvs =
  mk-span "Hole" pi (posinfo-plus pi 1) 
    (ll-data-term :: error-data "This hole remains to be filled in" :: expected-kind-if Γ k ++ tvs)


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
                                     else ("Number of rewrites", [[ ℕ-to-string numrewrites ]] , [])) ::
                                     [ explain ("Rewrite terms in the " 
                                             ^ expected-to-string expected ^ " type, using an equation. "
                                             ^ (if (is-rho-plus r) then "" else "Do not ") ^ "Beta-reduce the type as we look for matches.") ]))

Phi-span : posinfo → posinfo → checking-mode → 𝕃 tagged-val → span
Phi-span pi pi' expected tvs = mk-span "Phi" pi pi' (checking-data expected :: ll-data-term :: tvs)

Chi-span : ctxt → posinfo → maybeAtype → term → checking-mode → 𝕃 tagged-val → span
Chi-span Γ pi m t' check tvs = mk-span "Chi" pi (term-end-pos t')  (ll-data-term :: checking-data check :: tvs ++ helper m)
  where helper : maybeAtype → 𝕃 tagged-val
        helper (Atype T) =  explain ("Check a term against an asserted type") :: [ to-string-tag "the asserted type" Γ T ]
        helper NoAtype = [ explain ("Change from checking mode (outside the term) to synthesizing (inside)") ] 

Sigma-span : ctxt → posinfo → term → maybe type → 𝕃 tagged-val → span
Sigma-span Γ pi t expected tvs =
  mk-span "Sigma" pi (term-end-pos t) 
     (ll-data-term :: checking-data (maybe-to-checking expected) :: tvs ++
     (explain ("Swap the sides of the equation synthesized for the body of this term.")
     :: expected-type-if Γ expected))

motive-label : string
motive-label = "the motive"

the-motive : ctxt → type → tagged-val
the-motive = to-string-tag motive-label

Theta-span : ctxt → posinfo → theta → term → lterms → checking-mode → 𝕃 tagged-val → span
Theta-span Γ pi u t ls check tvs = mk-span "Theta" pi (lterms-end-pos ls) (ll-data-term :: checking-data check :: tvs ++ do-explain u)
  where do-explain : theta → 𝕃 tagged-val
        do-explain Abstract = [ explain ("Perform an elimination with the first term, after abstracting it from the expected type.") ]
        do-explain (AbstractVars vs) = [ strRunTag "explanation" Γ (strAdd "Perform an elimination with the first term, after abstracting the listed variables (" ≫str vars-to-string vs ≫str strAdd ") from the expected type.") ]
        do-explain AbstractEq = [ explain ("Perform an elimination with the first term, after abstracting it with an equation " 
                                         ^ "from the expected type.") ]

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

IotaPair-span : posinfo → posinfo → checking-mode → 𝕃 tagged-val → span
IotaPair-span pi pi' c tvs =
  mk-span "Iota pair" pi pi' (explain "Inhabit a iota-type (dependent intersection type)." :: checking-data c :: ll-data-term :: tvs)

IotaProj-span : term → posinfo → checking-mode → 𝕃 tagged-val → span
IotaProj-span t pi' c tvs = mk-span "Iota projection" (term-start-pos t) pi' (checking-data c :: ll-data-term :: tvs)

Omega-span : posinfo → term → checking-mode → 𝕃 tagged-val → span
Omega-span pi t c tvs = mk-span "Omega term" pi (term-end-pos t) (explain "A weak form of extensionality: derive an equation between lambda-abstractions from a ∀-quantified equation." :: ll-data-term :: checking-data c :: tvs)

Let-span : ctxt → checking-mode → posinfo → defTermOrType → term → 𝕃 tagged-val → span
Let-span Γ c pi d t' tvs = mk-span "Let-term" pi (term-end-pos t') (binder-data-const :: bound-data d Γ :: ll-data-term :: checking-data c :: tvs)
