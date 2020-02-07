import cedille-options
open import general-util
module spans (options : cedille-options.options) {mF : Set → Set} {{mFm : monad mF}} where
open import cedille-types
open import constants 
open import conversion (cedille-options.options.disable-conv options) using (conv-type ; conv-kind ; hnf ; unfold-all)
open import ctxt
open import free-vars
open import syntax-util
open import type-util
open import to-string options
open import subst
open import datatype-util
open import json


--------------------------------------------------
-- span datatype
--------------------------------------------------

err-m : Set
err-m = maybe string

data span : Set where
  mk-span : string → posinfo → posinfo → 𝕃 tagged-val {- extra information for the span -} → err-m → span

span-to-json : span → json
span-to-json (mk-span name s e tvs err?) =
  json-array $ json-string name :: json-raw [[ s ]] :: json-raw [[ e ]] :: [ tagged-vals-to-json (maybe-else' err? tvs λ err → ("error" , [[ err ]] , []) :: tvs) ]

data error-span : Set where
  mk-error-span : string → posinfo → posinfo → 𝕃 tagged-val → string → error-span

data spans : Set where
  regular-spans : maybe error-span → 𝕃 span → spans
  global-error : string {- error message -} → maybe span → spans

is-error-span : span → 𝔹
is-error-span (mk-span _ _ _ _ err) = isJust err

get-span-error : span → err-m
get-span-error (mk-span _ _ _ _ err) = err

get-spans-error : spans → maybe (string × 𝕃 tagged-val)
get-spans-error (global-error e _) = just $ e , []
get-spans-error (regular-spans e? _) = maybe-map (λ {(mk-error-span _ _ _ tvs e) → e , tvs}) e?

get-tagged-vals : span → 𝕃 tagged-val
get-tagged-vals (mk-span _ _ _ tvs _) = tvs

spans-have-error : spans → 𝔹
spans-have-error (regular-spans es ss) = isJust es
spans-have-error (global-error _ _) = tt

empty-spans : spans
empty-spans = regular-spans nothing []

spans-to-json' : spans → 𝕃 (string × json)
spans-to-json' (regular-spans _ ss) = [ "spans" , json-array (map span-to-json ss) ]
spans-to-json' (global-error e s) =
  ("error" , json-string e) :: maybe-else' s [] λ s → [ "global-error" , span-to-json s ]

spans-to-json : spans → json
spans-to-json = json-object ∘ spans-to-json'

print-file-id-table : ctxt → 𝕃 tagged-val
print-file-id-table Γ = h [] (ctxt.id-list Γ) where
  h : ∀ {i} → 𝕃 tagged-val → 𝕍 string i → 𝕃 tagged-val
  h ts [] = ts
  h {i} ts (fn :: fns) = h (strRunTag "fileid" empty-ctxt (strAdd fn) :: ts) fns

add-span : span → spans → spans
add-span s@(mk-span dsc pi pi' tv nothing) (regular-spans es ss) =
  regular-spans es (s :: ss)
add-span s@(mk-span dsc pi pi' tv (just err)) (regular-spans es ss) =
  regular-spans (just (mk-error-span dsc pi pi' tv err)) (s :: ss)
add-span s (global-error e e') =
  global-error e e'

--------------------------------------------------
-- spanM, a state monad for spans
--------------------------------------------------


spanM : Set → Set
spanM A = spans → mF (A × spans)

instance
  spanM-monad : monad spanM
  return ⦃ spanM-monad ⦄ = curry return
  _>>=_ ⦃ spanM-monad ⦄ m₁ m₂ ss = m₁ ss >>= uncurry m₂

  spanM-functor : functor spanM
  fmap ⦃ spanM-functor ⦄ g m ss = m ss >>= uncurry λ a ss' → return (g a , ss')

  spanM-applicative : applicative spanM
  pure ⦃ spanM-applicative ⦄ = return
  _<*>_ ⦃ spanM-applicative ⦄ mab ma ss =
    mab ss >>= uncurry λ f ss₁ →
    ma ss₁ >>= uncurry λ a →
    return (f a)

spanMok : spanM ⊤
spanMok = return triv

get-error : ∀ {A : Set} → (maybe error-span → spanM A) → spanM A
get-error m ss@(global-error _ _) = m nothing ss
get-error m ss@(regular-spans nothing _) = m nothing ss
get-error m ss@(regular-spans (just es) _) = m (just es) ss

set-error : maybe (error-span) → spanM ⊤
set-error es ss@(global-error _ _) = return2 triv ss
set-error es (regular-spans _ ss) = return2 triv (regular-spans es ss)

spanM-push : ∀ {A} → mF A → spanM A
spanM-push mf ss = mf >>= λ a → return2 a ss

-- discard changes made by the first computation
_>>=spand_ : ∀{A B : Set} → spanM A → (A → spanM B) → spanM B
_>>=spand_{A} m m' ss = m ss >>= λ where (v , _) → m' v ss

spanM-add : span → spanM ⊤
spanM-add s ss = return (triv , add-span s ss)

infixr 2 [-_-]_
[-_-]_ : ∀ {X} → span → spanM X → spanM X
[- s -] m = spanM-add s >> m

debug-span : posinfo → posinfo → 𝕃 tagged-val → span
debug-span pi pi' tvs = mk-span "Debug" pi pi' tvs nothing

spanM-debug : posinfo → posinfo → 𝕃 tagged-val → spanM ⊤
--spanM-debug pi pi' tvs = spanM-add (debug-span pi pi' tvs)
spanM-debug pi pi' tvs = spanMok

check-ret : ∀ {Y : Set} → maybe Y → Set → Set
check-ret {Y} T t = if isJust T then t else (t × Y)

return-when : ∀ {X Y} {m : maybe Y} → X → Y → spanM (check-ret m X)
return-when {X} {Y} {nothing} x u = return2 x u
return-when {X} {Y} {just _} x u = return x

case-ret : ∀ {X Y} {m : maybe Y} → spanM (X × Y) → (Y → spanM X) → spanM (check-ret m X)
case-ret {X} {Y} {nothing} n j = n
case-ret {X} {Y} {just y} n j = j y

case-ret-body : ∀ {X Y} {m : maybe Y} → spanM (check-ret m X) → (X → Y → spanM (check-ret m X)) → spanM (check-ret m X)
case-ret-body {X} {Y} {nothing} m f = m >>= uncurry f
case-ret-body {X} {Y} {just y} m f = m >>= λ x → f x y

with-clear-error : ∀ {A} → spanM A → spanM A
with-clear-error m =
  get-error λ es → set-error nothing >> m >>= λ a → set-error es >> return a


--------------------------------------------------
-- tagged-val constants
--------------------------------------------------

to-string-tag-tk : (tag : string) → ctxt → tpkd → tagged-val
to-string-tag-tk t Γ (Tkt T) = to-string-tag t Γ T
to-string-tag-tk t Γ (Tkk k) = to-string-tag t Γ k

location-data : location → tagged-val
location-data (file-name , pi) = strRunTag "location" empty-ctxt (strAdd file-name >>str strAdd " - " >>str strAdd pi)

var-location-data : ctxt → var → tagged-val
var-location-data Γ x =
  location-data (maybe-else missing-location snd
    (trie-lookup (ctxt.i Γ) x ||-maybe trie-lookup (ctxt.i Γ) (qualif-var Γ x)))

explain : string → tagged-val
explain = strRunTag "explanation" empty-ctxt ∘ strAdd

reason : string → tagged-val
reason = strRunTag "reason" empty-ctxt ∘ strAdd

expected-type : ctxt → type → tagged-val
expected-type = to-string-tag "expected-type"

expected-type-subterm : ctxt → type → tagged-val
expected-type-subterm = to-string-tag "expected-type of the subterm"

missing-expected-type : tagged-val
missing-expected-type = strRunTag "expected-type" empty-ctxt $ strAdd "[missing]"

expected-kind : ctxt → kind → tagged-val
expected-kind = to-string-tag "expected kind"

expected-kind-if : ctxt → maybe kind → 𝕃 tagged-val
expected-kind-if _ nothing = []
expected-kind-if Γ (just k) = [ expected-kind Γ k ]

expected-type-if : ctxt → maybe type → 𝕃 tagged-val
expected-type-if _ nothing = []
expected-type-if Γ (just tp) = [ expected-type Γ tp ]

type-data : ctxt → type → tagged-val
type-data = to-string-tag "type"

type-data-if : ctxt → maybe type → 𝕃 tagged-val
type-data-if Γ = maybe-else [] λ T → [ type-data Γ T ]

warning-data : string → tagged-val
warning-data = strRunTag "warning" empty-ctxt ∘ strAdd

check-for-type-mismatch : ctxt → string → type → type → err-m
check-for-type-mismatch Γ s tp tp' =
  if conv-type Γ tp tp' then nothing else just ("The expected type does not match the " ^ s ^ " type")

check-for-type-mismatch-if : ctxt → string → maybe type → type → err-m
check-for-type-mismatch-if Γ s T? T = T? >>= check-for-type-mismatch Γ s T

check-for-kind-mismatch : ctxt → string → kind → kind → err-m
check-for-kind-mismatch Γ s kd kd' =
  if conv-kind Γ kd kd' then nothing else just ("The expected kind does not match the " ^ s ^ " kind")

check-for-kind-mismatch-if : ctxt → string → maybe kind → kind → err-m
check-for-kind-mismatch-if Γ s k? k = k? >>= check-for-kind-mismatch Γ s k

check-for-tpkd-mismatch-if : ctxt → string → maybe tpkd → tpkd → err-m
check-for-tpkd-mismatch-if Γ check tk? tk =
  tk? >>= either-else
    (either-else' tk (check-for-type-mismatch Γ check)
      λ kd tp → just "Expected a kind classifier, but got a type")
    (either-else' tk (λ tp kd → just "Expected a type classifier, but got a kind")
      (check-for-kind-mismatch Γ check))

summary-data : {ed : exprd} → (name : string) → ctxt → ⟦ ed ⟧ → tagged-val
summary-data name Γ t = strRunTag "summary" Γ (strVar name >>str strAdd " : " >>str to-stringe t)

head-kind : ctxt → kind → tagged-val
head-kind = to-string-tag "the kind of the head"

head-type : ctxt → type → tagged-val
head-type = to-string-tag "the type of the head"

arg-type : ctxt → type → tagged-val
arg-type = to-string-tag "computed arg type"

arg-exp-type : ctxt → type → tagged-val
arg-exp-type = to-string-tag "expected arg type"

type-app-head : ctxt → type → tagged-val
type-app-head = to-string-tag "the head"

term-app-head : ctxt → term → tagged-val
term-app-head = to-string-tag "the head"

term-argument : ctxt → term → tagged-val
term-argument = to-string-tag "the argument"

type-argument : ctxt → type → tagged-val
type-argument = to-string-tag "the argument"

contextual-type-argument : ctxt → type → tagged-val
contextual-type-argument = to-string-tag "contextual type arg"

arg-argument : ctxt → arg → tagged-val
arg-argument Γ = either-else (term-argument Γ) (type-argument Γ) ∘ arg-to-tmtp

kind-data : ctxt → kind → tagged-val
kind-data = to-string-tag "kind"

kind-data-if : ctxt → maybe kind → 𝕃 tagged-val
kind-data-if Γ (just k) = [ kind-data Γ k ]
kind-data-if _ nothing = []

super-kind-data : tagged-val
super-kind-data = strRunTag "superkind" empty-ctxt $ strAdd "□"

symbol-data : string → tagged-val
symbol-data = strRunTag "symbol" empty-ctxt ∘ strAdd

tk-data : ctxt → tpkd → tagged-val
tk-data Γ (Tkk k) = kind-data Γ k
tk-data Γ (Tkt t) = type-data Γ t

checking-to-string : checking-mode → string
checking-to-string checking = "checking"
checking-to-string synthesizing = "synthesizing"
checking-to-string untyped = "untyped"

checking-data : checking-mode → tagged-val
checking-data = strRunTag "checking-mode" empty-ctxt ∘' strAdd ∘' checking-to-string

checked-meta-var : var → tagged-val
checked-meta-var = strRunTag "checked meta-var" empty-ctxt ∘ strAdd

ll-data : exprd → tagged-val
ll-data = strRunTag "language-level" empty-ctxt ∘' strAdd ∘' exprd-name

ll-data-term = ll-data TERM
ll-data-type = ll-data TYPE
ll-data-kind = ll-data KIND

binder-data : ctxt → posinfo → var → (atk : tpkd) → erased? → maybe (if tk-is-type atk then term else type) → (from to : posinfo) → tagged-val
binder-data Γ pi x atk me val s e =
  strRunTag "binder" Γ $
  strAdd "symbol:" >>str
  strAdd x >>str
  atk-val atk val >>str
  strAdd "§from:" >>str
  strAdd s >>str
  strAdd "§to:" >>str
  strAdd e >>str
  loc >>str
  strErased?
  where
  loc : strM
  loc = strAdd "§fn:" >>str strAdd (ctxt.fn Γ) >>str strAdd "§pos:" >>str strAdd pi
  strErased? : strM
  strErased? =
    strAdd "§erased:" >>str
    strAdd (if me then "true" else "false")
  val? : ∀ {ed} → maybe ⟦ ed ⟧ → strM
  val? = maybe-else strEmpty λ x →
    strAdd "§value:" >>str
    to-stringe x
  atk-val : (atk : tpkd) → maybe (if tk-is-type atk then term else type) → strM
  atk-val (Tkt T) t? =
    strAdd "§type:" >>str
    to-stringe T >>str
    val? t?
  atk-val (Tkk k) T? =
    strAdd "§kind:" >>str
    to-stringe k >>str
    val? T?

punctuation-data : tagged-val
punctuation-data = strRunTag "punctuation" empty-ctxt $ strAdd "true"

not-for-navigation : tagged-val
not-for-navigation = strRunTag "not-for-navigation" empty-ctxt $ strAdd "true"

is-erased : type → 𝔹
is-erased (TpVar _) = tt
is-erased _ = ff

keywords = "keywords"
keyword-application = "application"
keyword-locale = "meta-var-locale"

keywords-data : 𝕃 string → tagged-val
keywords-data kws = keywords , h kws , [] where
  h : 𝕃 string → rope
  h [] = [[]]
  h (k :: []) = [[ k ]]
  h (k :: ks) = [[ k ]] ⊹⊹ [[ " " ]] ⊹⊹ h ks

keywords-app : (is-locale : 𝔹) → tagged-val
keywords-app l = keywords-data ([ keyword-application ] ++ (if l then [ keyword-locale ] else []))

keywords-app-if-typed : checking-mode → (is-locale : 𝔹) → 𝕃 tagged-val
keywords-app-if-typed untyped l = []
keywords-app-if-typed _ l = [ keywords-app l ]

error-if-not-eq : ctxt → type → 𝕃 tagged-val → 𝕃 tagged-val × err-m
error-if-not-eq Γ (TpEq t1 t2) tvs = expected-type Γ (TpEq t1 t2) :: tvs , nothing
error-if-not-eq Γ tp tvs = expected-type Γ tp :: tvs , just "This term is being checked against the following type, but an equality type was expected"

error-if-not-eq-maybe : ctxt → maybe type → 𝕃 tagged-val → 𝕃 tagged-val × err-m
error-if-not-eq-maybe Γ (just tp) = error-if-not-eq Γ tp
error-if-not-eq-maybe _ _ tvs = tvs , nothing

params-data : ctxt → params → 𝕃 tagged-val
params-data _ [] = []
params-data Γ ps = [ params-to-string-tag "parameters" Γ ps ]

--------------------------------------------------
-- span-creating functions
--------------------------------------------------

Star-name : string
Star-name = "Star"

parens-span : posinfo → posinfo → span
parens-span pi pi' = mk-span "parentheses" pi pi' [] nothing

data decl-class : Set where
  decl-param : decl-class
  decl-index : decl-class 

decl-class-name : decl-class → string
decl-class-name decl-param = "parameter"
decl-class-name decl-index = "index"

Decl-span : ctxt → decl-class → posinfo → posinfo → var → tpkd → erased? → posinfo → posinfo → span
Decl-span Γ dc pi pi' v atk me pi'' pi''' = mk-span ((if tk-is-type atk then "Term " else "Type ") ^ (decl-class-name dc))
                                      pi pi''' [ binder-data Γ pi' v atk me nothing pi'' pi''' ] nothing

TpVar-span : ctxt → posinfo → string → checking-mode → 𝕃 tagged-val → err-m → span
TpVar-span Γ pi v check tvs =
  mk-span name pi (posinfo-plus-str pi (unqual-local v))
    (checking-data check :: ll-data-type :: var-location-data Γ v :: symbol-data (unqual-local v) :: tvs)
  where
  v' = unqual-local v
  name = if stringset-contains (ctxt.μ̲ Γ) (qualif-var Γ v)
           then "Datatype variable"
           else "Type variable"

Var-span : ctxt → posinfo → string → checking-mode → 𝕃 tagged-val → err-m → span
Var-span Γ pi v check tvs =
  mk-span name pi (posinfo-plus-str pi v')
    (checking-data check :: ll-data-term :: var-location-data Γ v :: symbol-data v' :: tvs)
  where
  v' = unqual-local v
  name : string
  name with qual-lookup Γ v'
  ...| just (_ , _ , ctr-def _ _ _ _ _ , _) = "Constructor variable"
  ...| _ = "Term variable"

KdVar-span : ctxt → (posinfo × var) → (end-pi : posinfo) → params → checking-mode → 𝕃 tagged-val → err-m → span
KdVar-span Γ (pi , v) pi' ps check tvs =
  mk-span "Kind variable" pi pi'
    (checking-data check :: ll-data-kind :: var-location-data Γ v :: symbol-data (unqual-local v) :: super-kind-data :: (params-data Γ ps ++ tvs))

var-span-with-tags : erased? → ctxt → posinfo → string → checking-mode → tpkd → 𝕃 tagged-val → err-m → span
var-span-with-tags _ Γ pi x check (Tkk k) tags = TpVar-span Γ pi x check ({-keywords-data-var ff ::-} [ kind-data Γ k ] ++ tags)
var-span-with-tags e Γ pi x check (Tkt t) tags = Var-span Γ pi x check ({-keywords-data-var e ::-} [ type-data Γ t ] ++ tags)

var-span :  erased? → ctxt → posinfo → string → checking-mode → tpkd → err-m → span
var-span e Γ pi x check tk = var-span-with-tags e Γ pi x check tk []

redefined-var-span : ctxt → posinfo → var → span
redefined-var-span Γ pi x = mk-span "Variable definition" pi (posinfo-plus-str pi x)
                             [ var-location-data Γ x ] (just "This symbol was defined already")

TpAppt-span : posinfo → posinfo → checking-mode → 𝕃 tagged-val → err-m → span
TpAppt-span pi pi' check tvs = mk-span "Application of a type to a term" pi pi' (checking-data check :: ll-data-type :: tvs)

TpApp-span : posinfo → posinfo → checking-mode → 𝕃 tagged-val → err-m → span
TpApp-span pi pi' check tvs = mk-span "Application of a type to a type" pi pi' (checking-data check :: ll-data-type :: tvs)

App-span : (is-locale : 𝔹) → posinfo → posinfo → checking-mode → 𝕃 tagged-val → err-m → span
App-span l pi pi' check tvs = mk-span "Application of a term to a term" pi pi' (checking-data check :: ll-data-term :: keywords-app-if-typed check l ++ tvs)

AppTp-span : (is-locale : 𝔹) → posinfo → posinfo → checking-mode → 𝕃 tagged-val → err-m → span
AppTp-span l pi pi' check tvs = mk-span "Application of a term to a type" pi pi' (checking-data check :: ll-data-term :: keywords-app-if-typed check l ++ tvs)

TpQuant-span : ctxt → erased? → posinfo → posinfo → var → tpkd → ex-tp → checking-mode → 𝕃 tagged-val → err-m → span
TpQuant-span Γ me pi pi' x atk body check tvs err =
  let err-if-type-pi = ifMaybej ( ~ (tk-is-type atk || me))
                          "Π-types must bind a term, not a type (use ∀ instead)"
      name = if me then "Implicit dependent function type" else "Dependent function type" in
  mk-span name pi (type-end-pos body) (checking-data check :: ll-data-type :: binder-data Γ pi' x atk me nothing (type-start-pos body) (type-end-pos body) :: tvs) (if isJust err-if-type-pi then err-if-type-pi else err)

TpLambda-span : ctxt → posinfo → posinfo → var → tpkd → ex-tp → checking-mode → 𝕃 tagged-val → err-m → span
TpLambda-span Γ pi pi' x atk body check tvs =
  mk-span "Type-level lambda abstraction" pi (type-end-pos body)
    (checking-data check :: ll-data-type :: binder-data Γ pi' x atk NotErased nothing (type-start-pos body) (type-end-pos body) :: tvs)

Iota-span : ctxt → posinfo → posinfo → var → type → ex-tp → checking-mode → 𝕃 tagged-val → err-m → span
Iota-span Γ pi pi' x t1 t2 check tvs = mk-span "Iota-abstraction" pi (type-end-pos t2) (explain "A dependent intersection type" :: checking-data check :: binder-data Γ pi' x (Tkt t1) ff nothing (type-start-pos t2) (type-end-pos t2) :: ll-data-type :: tvs)

TpArrow-span : ex-tp → ex-tp → checking-mode → 𝕃 tagged-val → err-m → span
TpArrow-span t1 t2 check tvs = mk-span "Arrow type" (type-start-pos t1) (type-end-pos t2) (checking-data check :: ll-data-type :: tvs)

TpEq-span : posinfo → posinfo → checking-mode → 𝕃 tagged-val → err-m → span
TpEq-span pi pi' check tvs = mk-span "Equation" pi pi'
                             (explain "Equation between terms" :: checking-data check :: ll-data-type :: tvs)

Star-span : posinfo → checking-mode → err-m → span
Star-span pi check = mk-span Star-name pi (posinfo-plus pi 1) (checking-data check :: [ ll-data-kind ])

KdAbs-span : ctxt → posinfo → posinfo → var → tpkd → ex-kd → checking-mode → err-m → span
KdAbs-span Γ pi pi' x atk k check =
  mk-span "Pi kind" pi (kind-end-pos k)
    (checking-data check :: ll-data-kind :: binder-data Γ pi' x atk ff nothing (kind-start-pos k) (kind-end-pos k) :: [ super-kind-data ])

KdArrow-span : ex-tk → ex-kd → checking-mode → err-m → span
KdArrow-span k k' check = mk-span "Arrow kind" (tk-start-pos k) (kind-end-pos k') (checking-data check :: ll-data-kind :: [ super-kind-data ])

{- [[file:../cedille-mode.el::(defun%20cedille-mode-filter-out-special(data)][Frontend]]  -}
special-tags : 𝕃 string
special-tags =
  "symbol" :: "location" :: "language-level" :: "checking-mode" :: "summary"
  :: "binder" :: "bound-value" :: "keywords" :: []

error-span-filter-special : error-span → error-span
error-span-filter-special (mk-error-span dsc pi pi' tvs msg) =
  mk-error-span dsc pi pi' tvs' msg
  where tvs' = (flip filter) tvs λ tag → list-any (_=string (fst tag)) special-tags

erasure : ctxt → term → tagged-val
erasure Γ t = to-string-tag "erasure" Γ (erase t)

erased-marg-span : ctxt → posinfo → posinfo → maybe type → span
erased-marg-span Γ pi pi' mtp = mk-span "Erased module parameter" pi pi'
  (maybe-else [] (λ tp → [ type-data Γ tp ]) mtp)
  (just "An implicit module parameter variable occurs free in the erasure of the term")

Lam-span-erased : erased? → string
Lam-span-erased Erased = "Erased lambda abstraction (term-level)"
Lam-span-erased NotErased = "Lambda abstraction (term-level)"

Lam-span : ctxt → checking-mode → posinfo → posinfo → erased? → var → tpkd → ex-tm → 𝕃 tagged-val → err-m → span
Lam-span Γ c pi pi' l x atk t tvs = mk-span (Lam-span-erased l) pi (term-end-pos t) 
                                           (ll-data-term :: binder-data Γ pi' x atk l nothing (term-start-pos t) (term-end-pos t) :: checking-data c :: tvs)

compileFail-in : ctxt → term → 𝕃 tagged-val × err-m
compileFail-in Γ t with is-free-in compileFail-qual | t
...| is-free | tₒ with erase tₒ | hnf Γ (record unfold-all { unfold-defs = ff }) tₒ
...| tₑ | tₙ with is-free tₒ
...| ff = [] , nothing
...| tt with is-free tₙ | is-free tₑ
...| tt | _ = [ to-string-tag "normalized term" Γ tₙ ] , just "compileFail occurs in the normalized term"
...| ff | ff = [ to-string-tag "the term" Γ tₒ ] , just "compileFail occurs in an erased position"
...| ff | tt = [] , nothing


DefTerm-span : ctxt → posinfo → var → (checked : checking-mode) → maybe type → term → posinfo → 𝕃 tagged-val → span
DefTerm-span Γ pi x checked tp t pi' tvs = 
  h ((h-summary tp) ++ ({-erasure Γ t ::-} tvs)) pi x checked tp pi'
  where h : 𝕃 tagged-val → posinfo → var → (checked : checking-mode) → maybe type → posinfo → span
        h tvs pi x checking _ pi' = 
          mk-span "Term-level definition (checking)" pi pi' tvs nothing
        h tvs pi x _ (just tp) pi' = 
          mk-span "Term-level definition (synthesizing)" pi pi' (to-string-tag "synthesized type" Γ tp :: tvs) nothing
        h tvs pi x _ nothing pi' = 
          mk-span "Term-level definition (synthesizing)" pi pi' ((strRunTag "synthesized type" empty-ctxt $ strAdd "[nothing]") :: tvs) nothing
        h-summary : maybe type → 𝕃 tagged-val
        h-summary nothing = [(checking-data synthesizing)]
        h-summary (just tp) = (checking-data checking :: [ summary-data x Γ tp ])
    
CheckTerm-span : ctxt → (checked : checking-mode) → maybe type → ex-tm → posinfo → 𝕃 tagged-val → span
CheckTerm-span Γ checked tp t pi' tvs = 
  h ({-erasure Γ t ::-} tvs) checked tp (term-start-pos t) pi'
  where h : 𝕃 tagged-val → (checked : checking-mode) → maybe type → posinfo → posinfo → span
        h tvs checking _ pi pi' = 
          mk-span "Checking a term" pi pi' (checking-data checking :: tvs) nothing
        h tvs _ (just tp) pi pi' = 
          mk-span "Synthesizing a type for a term" pi pi' (checking-data synthesizing :: to-string-tag "synthesized type" Γ tp :: tvs) nothing
        h tvs _ nothing pi pi' = 
          mk-span "Synthesizing a type for a term" pi pi' (checking-data synthesizing :: (strRunTag "synthesized type" empty-ctxt $ strAdd "[nothing]") :: tvs) nothing

normalized-type : ctxt → type → tagged-val
normalized-type = to-string-tag "normalized type"

DefType-span : ctxt → posinfo → var → (checked : checking-mode) → maybe kind → type → posinfo → 𝕃 tagged-val → span
DefType-span Γ pi x checked mk tp pi' tvs =
  h ((h-summary mk) ++ tvs) checked mk
  where h : 𝕃 tagged-val → checking-mode → maybe kind → span
        h tvs checking _ = mk-span "Type-level definition (checking)" pi pi' tvs nothing
        h tvs _ (just k) =
          mk-span "Type-level definition (synthesizing)" pi pi' (to-string-tag "synthesized kind" Γ k :: tvs) nothing
        h tvs _ nothing =
          mk-span "Type-level definition (synthesizing)" pi pi' ( (strRunTag "synthesized kind" empty-ctxt $ strAdd "[nothing]") :: tvs) nothing
        h-summary : maybe kind → 𝕃 tagged-val
        h-summary nothing = [(checking-data synthesizing)]
        h-summary (just k) = (checking-data checking :: [ summary-data x Γ k ])

DefKind-span : ctxt → posinfo → var → kind → posinfo → span
DefKind-span Γ pi x k pi' = mk-span "Kind-level definition" pi pi' (kind-data Γ k :: [ summary-data x Γ (Var "□") ]) nothing

DefDatatype-span : ctxt → posinfo → posinfo → var → params → (reg Mu bound : kind) → (mu : type) → (cast : type) → ctrs → ex-kd → posinfo → span
DefDatatype-span Γ pi pi' x ps k kₘᵤ kₓ Tₘᵤ Tₜₒ cs kₑₓ pi'' =
  mk-span "Datatype definition" pi pi'' (binder-data Γ pi' x (Tkk kₓ) ff nothing (kind-end-pos kₑₓ) pi'' :: summary-data x Γ k :: summary-data (data-Is/ x) Γ kₘᵤ :: summary-data (data-is/ x) Γ Tₘᵤ :: summary-data (data-to/ x) Γ Tₜₒ :: to-string-tag (data-Is/ x) Γ kₘᵤ :: to-string-tag (data-is/ x) Γ Tₘᵤ :: to-string-tag (data-to/ x) Γ Tₜₒ :: []) nothing

{-unchecked-term-span : term → span
unchecked-term-span t = mk-span "Unchecked term" (term-start-pos t) (term-end-pos t)
                           (ll-data-term :: not-for-navigation :: [ explain "This term has not been type-checked"]) nothing-}

Beta-span : posinfo → posinfo → checking-mode → 𝕃 tagged-val → err-m → span
Beta-span pi pi' check tvs = mk-span "Beta axiom" pi pi'
                     (checking-data check :: ll-data-term :: explain "A term constant whose type states that β-equal terms are provably equal" :: tvs)

hole-span : ctxt → posinfo → maybe type → checking-mode → 𝕃 tagged-val → span
hole-span Γ pi tp check tvs = 
  mk-span "Hole" pi (posinfo-plus pi 1)
    (checking-data check :: ll-data-term :: expected-type-if Γ tp ++ tvs)
    (just "This hole remains to be filled in")

tp-hole-span : ctxt → posinfo → maybe kind → checking-mode → 𝕃 tagged-val → span
tp-hole-span Γ pi k check tvs =
  mk-span "Hole" pi (posinfo-plus pi 1)
    (checking-data check :: ll-data-type :: expected-kind-if Γ k ++ tvs)
    (just "This hole remains to be filled in")

kd-hole-span : posinfo → checking-mode → span
kd-hole-span pi check =
  mk-span "Hole" pi (posinfo-plus pi 1)
    (checking-data check :: ll-data-kind :: [])
    (just "This hole remains to be filled in")


expected-to-string : checking-mode → string
expected-to-string checking = "expected"
expected-to-string synthesizing = "synthesized"
expected-to-string untyped = "untyped"

Epsilon-span : posinfo → left-right → minus? → ex-tm → checking-mode → 𝕃 tagged-val → err-m → span
Epsilon-span pi lr m t check tvs = mk-span "Epsilon" pi (term-end-pos t) 
                                         (checking-data check :: ll-data-term :: tvs ++
                                         [ explain ("Normalize " ^ side lr ^ " of the " 
                                                   ^ expected-to-string check ^ " equation, using " ^ maybeMinus-description m 
                                                   ^ " reduction" ) ])
  where side : left-right → string
        side EpsLeft = "the left-hand side"
        side EpsRight = "the right-hand side"
        side EpsBoth = "both sides"
        maybeMinus-description : minus? → string
        maybeMinus-description EpsHnf = "head"
        maybeMinus-description EpsHanf = "head-applicative"

optGuide-spans : ctxt → maybe ex-guide → checking-mode → spanM ⊤
optGuide-spans Γ nothing _ = spanMok
optGuide-spans Γ (just (ExGuide pi x tp)) expected =
  spanM-add (Var-span Γ pi x expected [] nothing)

Rho-span : posinfo → ex-tm → ex-tm → checking-mode → 𝔹 → ℕ ⊎ var → 𝕃 tagged-val → err-m → span
Rho-span pi t t' expected r (inj₂ x) tvs =
  mk-span "Rho" pi (term-end-pos t')
    (checking-data expected :: ll-data-term :: explain ("Rewrite all places where " ^ x ^ " occurs in the " ^ expected-to-string expected ^ " type, using an equation. ") :: tvs)
Rho-span pi t t' expected r (inj₁ numrewrites) tvs err =
  mk-span "Rho" pi (term-end-pos t') 
    (checking-data expected :: ll-data-term :: tvs ++
    (explain ("Rewrite terms in the " 
      ^ expected-to-string expected ^ " type, using an equation. "
      ^ (if r then "" else "Do not ") ^ "Beta-reduce the type as we look for matches") :: fst h)) (snd h)
  where h : 𝕃 tagged-val × err-m
        h = if isJust err
              then [] , err
              else if numrewrites =ℕ 0
                then [] , just "No rewrites could be performed"
                else [ strRunTag "Number of rewrites" empty-ctxt (strAdd $ ℕ-to-string numrewrites) ] , err

Phi-span : posinfo → posinfo → checking-mode → 𝕃 tagged-val → err-m → span
Phi-span pi pi' expected tvs = mk-span "Phi" pi pi' (checking-data expected :: ll-data-term :: tvs)

Chi-span : ctxt → posinfo → maybe type → ex-tm → checking-mode → 𝕃 tagged-val → err-m → span
Chi-span Γ pi m t' check tvs = mk-span "Chi" pi (term-end-pos t')  (ll-data-term :: checking-data check :: tvs ++ helper m)
  where helper : maybe type → 𝕃 tagged-val
        helper (just T) =  explain ("Check a term against an asserted type") :: [ to-string-tag "the asserted type" Γ T ]
        helper nothing = [ explain ("Change from checking mode (outside the term) to synthesizing (inside)") ] 

VarSigma-span : posinfo → ex-tm → checking-mode → 𝕃 tagged-val → err-m → span
VarSigma-span pi t check tvs =
  mk-span "VarSigma" pi (term-end-pos t) 
     (ll-data-term :: checking-data check :: explain "Swap the sides of the equation synthesized for the body of this term" :: tvs)

Delta-span : posinfo → ex-tm → checking-mode → 𝕃 tagged-val → err-m → span
Delta-span pi t check tvs =
  mk-span "Delta" pi (term-end-pos t)
    (ll-data-term :: explain "Prove anything you want from a contradiction" :: checking-data check :: tvs)

Opaque-span : posinfo → posinfo → span
Opaque-span p₁ p₂ =
  mk-span "Opaque" p₁ p₂ [ explain "Mark a definition as opaque, for the purposes of conversion checking" ] nothing

Open-span : opacity → posinfo → var → ex-tm → checking-mode → 𝕃 tagged-val → err-m → span
Open-span o pi x t check tvs =
  elim-pair (if o
    then ("Open" , "Open an opaque definition")
    else ("Close" , "Hide a definition")) λ name expl →
  mk-span name pi (term-end-pos t)
    (ll-data-term :: explain expl :: checking-data check :: tvs)

motive-label : string
motive-label = "the motive"

the-motive : ctxt → type → tagged-val
the-motive = to-string-tag motive-label

Theta-span : ctxt → posinfo → theta → ex-tm → 𝕃 lterm → checking-mode → 𝕃 tagged-val → err-m → span
Theta-span Γ pi u t ls check tvs = mk-span "Theta" pi (lterms-end-pos (term-end-pos t) ls) (ll-data-term :: checking-data check :: tvs ++ do-explain u)
  where do-explain : theta → 𝕃 tagged-val
        do-explain Abstract = [ explain ("Perform an elimination with the first term, after abstracting it from the expected type") ]
        do-explain (AbstractVars vs) = [ strRunTag "explanation" Γ (strAdd "Perform an elimination with the first term, after abstracting the listed variables (" >>str vars-to-string vs >>str strAdd ") from the expected type") ]
        do-explain AbstractEq = [ explain ("Perform an elimination with the first term, after abstracting it with an equation " 
                                         ^ "from the expected type") ]

Mu-span : ctxt → posinfo → posinfo → (motive? : maybe type) → checking-mode → 𝕃 tagged-val → err-m → span
Mu-span Γ pi pi' motive? check tvs = mk-span "Mu" pi pi' (ll-data-term :: checking-data check :: explain ("Pattern match on a term" ^ (if isJust motive? then ", with a motive" else "")) :: tvs)

Sigma-span : ctxt → posinfo → posinfo → (motive? : maybe type) → checking-mode → 𝕃 tagged-val → err-m → span
Sigma-span Γ pi pi' motive? check tvs = mk-span "Sigma" pi pi' (ll-data-term :: checking-data check :: explain ("Pattern match on a term" ^ (if isJust motive? then ", with a motive" else "")) :: tvs)

pattern-span : posinfo → var → 𝕃 ex-case-arg → span
pattern-span pi x as = mk-span "Pattern" pi (snd $ foldr (λ a r → if fst r then r else (tt , (case a of λ {(ExCaseArg me pi x) → posinfo-plus-str pi x}))) (ff , posinfo-plus-str pi x) as) [] nothing

pattern-clause-span : posinfo → ex-tm → 𝕃 tagged-val → span
pattern-clause-span pi t tvs = mk-span "Pattern clause" pi (term-end-pos t) tvs nothing

pattern-ctr-span : ctxt → posinfo → var → case-args → 𝕃 tagged-val → err-m → span
pattern-ctr-span Γ pi x as tvs =
  mk-span "Pattern constructor" pi (posinfo-plus-str pi x) (checking-data synthesizing :: var-location-data Γ x :: ll-data-term :: symbol-data x :: args-data ++ tvs)
  where
  args-data : 𝕃 tagged-val
  args-data = if iszero (length as) then [] else [ params-to-string-tag "args" Γ (map (λ {(CaseArg me x tk?) → Param me x (maybe-else' tk? (Tkt (TpHole pi-gen)) id)}) as) ]


File-span : ctxt → posinfo → posinfo → string → span
File-span Γ pi pi' filename = mk-span ("Cedille source file (" ^ filename ^ ")") pi pi' (print-file-id-table Γ) nothing

Module-span : posinfo → posinfo → span
Module-span pi pi' = mk-span "Module declaration" pi pi' [ not-for-navigation ] nothing

Module-header-span : posinfo → posinfo → span
Module-header-span pi pi' = mk-span "Module header" pi pi' [ not-for-navigation ] nothing

DefDatatype-header-span : posinfo → span
DefDatatype-header-span pi = mk-span "Data" pi (posinfo-plus-str pi "data") [ not-for-navigation ] nothing

Import-span : posinfo → string → posinfo → 𝕃 tagged-val → err-m → span
Import-span pi file pi' tvs = mk-span ("Import of another source file") pi pi' (("Path" , [[ file ]] , []) :: location-data (file , first-position) :: tvs)

Import-module-span : ctxt → (posinfo × var) → params → 𝕃 tagged-val → err-m → span
Import-module-span Γ (pi , mn) ps tvs = mk-span "Imported module" pi (posinfo-plus-str pi mn) (params-data Γ ps ++ tvs)

punctuation-span : string → posinfo → posinfo → span
punctuation-span name pi pi'  = mk-span name pi pi' ( punctuation-data ::  not-for-navigation :: [] ) nothing

whitespace-span : posinfo → posinfo → span
whitespace-span pi pi'  = mk-span "Whitespace" pi pi' [ not-for-navigation ] nothing

comment-span : posinfo → posinfo → span
comment-span pi pi'  = mk-span "Comment" pi pi' [ not-for-navigation ] nothing

IotaPair-span : posinfo → posinfo → checking-mode → 𝕃 tagged-val → err-m → span
IotaPair-span pi pi' c tvs =
  mk-span "Iota pair" pi pi' (explain "Inhabit a iota-type (dependent intersection type)" :: checking-data c :: ll-data-term :: tvs)

IotaProj-span : ex-tm → posinfo → checking-mode → 𝕃 tagged-val → err-m → span
IotaProj-span t pi' c tvs = mk-span "Iota projection" (term-start-pos t) pi' (checking-data c :: ll-data-term :: tvs)

Let-span : erased? → posinfo → posinfo → checking-mode → 𝕃 tagged-val → err-m → span
Let-span me pi pi' c tvs =
  mk-span (if me then "Erased Term Let" else "Term Let") pi pi' (ll-data-term :: checking-data c :: tvs)

TpLet-span : posinfo → posinfo → checking-mode → 𝕃 tagged-val → span
TpLet-span pi pi' c tvs =
  mk-span "Type Let" pi pi' (ll-data-type :: checking-data c :: tvs) nothing
