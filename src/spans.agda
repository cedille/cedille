import cedille-options
open import general-util
module spans (options : cedille-options.options) {mF : Set → Set} {{_ : monad mF}} where

open import lib
open import functions

open import cedille-types
open import constants 
open import conversion
open import ctxt
open import free-vars
open import syntax-util
open import type-util
open import to-string options
open import subst
open import datatype-functions


--------------------------------------------------
-- span datatype
--------------------------------------------------

err-m : Set
err-m = maybe string

data span : Set where
  mk-span : string → posinfo → posinfo → 𝕃 tagged-val {- extra information for the span -} → err-m → span

span-to-rope : span → rope
span-to-rope (mk-span name start end extra nothing) = 
  [[ "[\"" ^ name ^ "\"," ^ start ^ "," ^ end ^ ",{" ]] ⊹⊹ tagged-vals-to-rope 0 extra ⊹⊹ [[ "}]" ]]
span-to-rope (mk-span name start end extra (just err)) = 
  [[ "[\"" ^ name ^ "\"," ^ start ^ "," ^ end ^ ",{" ]] ⊹⊹ tagged-vals-to-rope 0 (strRunTag "error" empty-ctxt (strAdd err) :: extra) ⊹⊹ [[ "}]" ]]

data error-span : Set where
  mk-error-span : string → posinfo → posinfo → 𝕃 tagged-val → string → error-span

data spans : Set where
  regular-spans : maybe error-span → 𝕃 span → spans
  global-error : string {- error message -} → maybe span → spans

is-error-span : span → 𝔹
is-error-span (mk-span _ _ _ _ err) = isJust err

get-span-error : span → err-m
get-span-error (mk-span _ _ _ _ err) = err

get-tagged-vals : span → 𝕃 tagged-val
get-tagged-vals (mk-span _ _ _ tvs _) = tvs

spans-have-error : spans → 𝔹
spans-have-error (regular-spans es ss) = isJust es
spans-have-error (global-error _ _) = tt

empty-spans : spans
empty-spans = regular-spans nothing []

𝕃span-to-rope : 𝕃 span → rope
𝕃span-to-rope (s :: []) = span-to-rope s
𝕃span-to-rope (s :: ss) = span-to-rope s ⊹⊹ [[ "," ]] ⊹⊹ 𝕃span-to-rope ss
𝕃span-to-rope [] = [[]]

spans-to-rope : spans → rope
spans-to-rope (regular-spans _ ss) = [[ "{\"spans\":["]] ⊹⊹ 𝕃span-to-rope ss ⊹⊹ [[ "]}" ]] where
spans-to-rope (global-error e s) =
  [[ global-error-string e ]] ⊹⊹ maybe-else [[]] (λ s → [[", \"global-error\":"]] ⊹⊹ span-to-rope s) s

print-file-id-table : ctxt → 𝕃 tagged-val
print-file-id-table (mk-ctxt mod (syms , mn-fn , mn-ps , fn-ids , id , id-fns) is Δ) =
  h [] id-fns where
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

-- return for the spanM monad
spanMr : ∀{A : Set} → A → spanM A
spanMr = curry returnM

spanMok : spanM ⊤
spanMok = spanMr triv

get-error : ∀ {A : Set} → (maybe error-span → spanM A) → spanM A
get-error m ss@(global-error _ _) = m nothing ss
get-error m ss@(regular-spans nothing _) = m nothing ss
get-error m ss@(regular-spans (just es) _) = m (just es) ss

set-error : maybe (error-span) → spanM ⊤
set-error es ss@(global-error _ _) = returnM (triv , ss)
set-error es (regular-spans _ ss) = returnM (triv , regular-spans es ss)

_≫=span_ : ∀{A B : Set} → spanM A → (A → spanM B) → spanM B
(m₁ ≫=span m₂) ss = m₁ ss ≫=monad λ where (v , ss) → m₂ v ss

_≫span_ : ∀{A B : Set} → spanM A → spanM B → spanM B
(m₁ ≫span m₂) = m₁ ≫=span (λ _ → m₂)

infixr 2 _≫span_ _≫=span_ _≫=spanj_ _≫=spanm_ _≫=spanm'_ _≫=spanc_ _≫=spanc'_ _≫spanc_ _≫spanc'_ _≫=span?_

_≫=span?_ : ∀{A B : Set} → maybe (spanM A) → (maybe A → spanM B) → spanM B
nothing ≫=span? f = f nothing
just a ≫=span? f = a ≫=span (f ∘ just)

_≫=spanj_ : ∀{A : Set} → spanM (maybe A) → (A → spanM ⊤) → spanM ⊤
_≫=spanj_{A} m m' = m ≫=span cont
  where cont : maybe A → spanM ⊤
        cont nothing = spanMok
        cont (just x) = m' x

-- discard changes made by the first computation
_≫=spand_ : ∀{A B : Set} → spanM A → (A → spanM B) → spanM B
_≫=spand_{A} m m' ss = m ss ≫=monad λ where (v , _) → m' v ss

_≫=spanm_ : ∀{A : Set} → spanM (maybe A) → (A → spanM (maybe A)) → spanM (maybe A)
_≫=spanm_{A} m m' = m ≫=span cont
  where cont : maybe A → spanM (maybe A)
        cont nothing = spanMr nothing
        cont (just a) = m' a

_≫=spans'_ : ∀ {A B E : Set} → spanM (E ∨ A) → (A → spanM (E ∨ B)) → spanM (E ∨ B)
_≫=spans'_ m f = m ≫=span λ where
  (inj₁ e) → spanMr (inj₁ e)
  (inj₂ a) → f a

_≫=spanm'_ : ∀{A B : Set} → spanM (maybe A) → (A → spanM (maybe B)) → spanM (maybe B)
_≫=spanm'_{A}{B} m m' = m ≫=span cont
  where cont : maybe A → spanM (maybe B)
        cont nothing = spanMr nothing
        cont (just a) = m' a


-- Currying/uncurry span binding
_≫=spanc_ : ∀{A B C} → spanM (A × B) → (A → B → spanM C) → spanM C
(m ≫=spanc m') ss = m ss ≫=monad λ where
  ((a , b) , ss') → m' a b ss'

_≫=spanc'_ : ∀{A B C} → spanM (A × B) → (B → spanM C) → spanM C
(m ≫=spanc' m') ss = m ss ≫=monad λ where
  ((a , b) , ss') → m' b ss'

_≫spanc'_ : ∀{A B} → spanM A → B → spanM (A × B)
(m ≫spanc' b) = m ≫=span λ a → spanMr (a , b)

_≫spanc_ : ∀{A B} → spanM A → spanM B → spanM (A × B)
(ma ≫spanc mb) = ma ≫=span λ a → mb ≫=span λ b → spanMr (a , b)

spanMok' : ∀{A} → A → spanM (⊤ × A)
spanMok' a = spanMr (triv , a)

_on-fail_≫=spanm'_ : ∀ {A B} → spanM (maybe A) → spanM B
                            → (A → spanM B) → spanM B
_on-fail_≫=spanm'_ {A}{B} m fail f = m ≫=span cont
  where cont : maybe A → spanM B
        cont nothing  = fail
        cont (just x) = f x

_on-fail_≫=spans'_ : ∀ {A B E} → spanM (E ∨ A) → (E → spanM B) → (A → spanM B) → spanM B
_on-fail_≫=spans'_ {A}{B}{E} m fail f = m ≫=span cont
  where cont : E ∨ A → spanM B
        cont (inj₁ err) = fail err
        cont (inj₂ a) = f a

_exit-early_≫=spans'_ = _on-fail_≫=spans'_

sequence-spanM : ∀ {A} → 𝕃 (spanM A) → spanM (𝕃 A)
sequence-spanM [] = spanMr []
sequence-spanM (sp :: sps)
  =   sp
    ≫=span λ x → sequence-spanM sps
    ≫=span λ xs → spanMr (x :: xs)

foldr-spanM : ∀ {A B} → (A → spanM B → spanM B) → spanM B → 𝕃 (spanM A) → spanM B
foldr-spanM f n [] = n
foldr-spanM f n (m :: ms)
  = m ≫=span λ a → f a (foldr-spanM f n ms)

foldl-spanM : ∀ {A B} → (spanM B → A → spanM B) → spanM B → 𝕃 (spanM A) → spanM B
foldl-spanM f m [] = m
foldl-spanM f m (m' :: ms) =
  m' ≫=span λ a → foldl-spanM f (f m a) ms

spanM-for_init_use_ : ∀ {A B} → 𝕃 (spanM A) → spanM B → (A → spanM B → spanM B) → spanM B
spanM-for xs init acc use f = foldr-spanM f acc xs

spanM-add : span → spanM ⊤
spanM-add s ss = returnM (triv , add-span s ss)

infixr 2 [-_-]_
[-_-]_ : ∀ {X} → span → spanM X → spanM X
[- s -] m = spanM-add s ≫span m

spanM-addl : 𝕃 span → spanM ⊤
spanM-addl [] = spanMok
spanM-addl (s :: ss) = spanM-add s ≫span spanM-addl ss

debug-span : posinfo → posinfo → 𝕃 tagged-val → span
debug-span pi pi' tvs = mk-span "Debug" pi pi' tvs nothing

spanM-debug : posinfo → posinfo → 𝕃 tagged-val → spanM ⊤
--spanM-debug pi pi' tvs = spanM-add (debug-span pi pi' tvs)
spanM-debug pi pi' tvs = spanMok


--------------------------------------------------
-- tagged-val constants
--------------------------------------------------

to-string-tag-tk : (tag : string) → ctxt → tpkd → tagged-val
to-string-tag-tk t Γ (Tkt T) = to-string-tag t Γ T
to-string-tag-tk t Γ (Tkk k) = to-string-tag t Γ k

location-data : location → tagged-val
location-data (file-name , pi) = strRunTag "location" empty-ctxt (strAdd file-name ≫str strAdd " - " ≫str strAdd pi)

var-location-data : ctxt → var → tagged-val
var-location-data Γ @ (mk-ctxt _ _ i _) x =
  location-data (maybe-else ("missing" , "missing") snd
    (trie-lookup i x maybe-or trie-lookup i (qualif-var Γ x)))
{-
{-# TERMINATING #-}
var-location-data : ctxt → var → maybe language-level → tagged-val
var-location-data Γ x (just ll-term) with ctxt-var-location Γ x | qualif-term Γ (Var posinfo-gen x)
...| ("missing" , "missing") | (Var pi x') = location-data (ctxt-var-location Γ x')
...| loc | _ = location-data loc
var-location-data Γ x (just ll-type) with ctxt-var-location Γ x | qualif-type Γ (TpVar posinfo-gen x)
...| ("missing" , "missing") | (TpVar pi x') = location-data (ctxt-var-location Γ x')
...| loc | _ = location-data loc
var-location-data Γ x (just ll-kind) with ctxt-var-location Γ x | qualif-kind Γ (KndVar posinfo-gen x ArgsNil)
...| ("missing" , "missing") | (KndVar pi x' as) = location-data (ctxt-var-location Γ x')
...| loc | _ = location-data loc
var-location-data Γ x nothing with ctxt-lookup-term-var Γ x | ctxt-lookup-type-var Γ x | ctxt-lookup-kind-var-def Γ x
...| just _ | _ | _ = var-location-data Γ x (just ll-term)
...| _ | just _ | _ = var-location-data Γ x (just ll-type)
...| _ | _ | just _ = var-location-data Γ x (just ll-kind)
...| _ | _ | _ = location-data ("missing" , "missing")
-}
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

-- hnf-type : ctxt → type → tagged-val
-- hnf-type Γ tp = to-string-tag "hnf of type" Γ (hnf-term-type Γ ff tp)

-- hnf-expected-type : ctxt → type → tagged-val
-- hnf-expected-type Γ tp = to-string-tag "hnf of expected type" Γ (hnf-term-type Γ ff tp)

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
check-for-type-mismatch-if Γ s T? T = T? ≫=maybe check-for-type-mismatch Γ s T

check-for-kind-mismatch : ctxt → string → kind → kind → err-m
check-for-kind-mismatch Γ s kd kd' =
  if conv-kind Γ kd kd' then nothing else just ("The expected kind does not match the " ^ s ^ " kind")

check-for-kind-mismatch-if : ctxt → string → maybe kind → kind → err-m
check-for-kind-mismatch-if Γ s k? k = k? ≫=maybe check-for-kind-mismatch Γ s k

summary-data : {ed : exprd} → (name : string) → ctxt → ⟦ ed ⟧ → tagged-val
summary-data name Γ t = strRunTag "summary" Γ (strVar name ≫str strAdd " : " ≫str to-stringe t)

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

--liftingType-data : ctxt → liftingType → tagged-val
--liftingType-data = to-string-tag "lifting type"

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

ll-data : language-level → tagged-val
ll-data = strRunTag "language-level" empty-ctxt ∘' strAdd ∘' ll-to-string

ll-data-term = ll-data ll-term
ll-data-type = ll-data ll-type
ll-data-kind = ll-data ll-kind
{-
binder-data : ℕ → tagged-val
binder-data n = "binder" , [[ ℕ-to-string n ]] , []

-- this is the subterm position in the parse tree (as determined by
-- spans) for the bound variable of a binder
binder-data-const : tagged-val
binder-data-const = binder-data 0

bound-data : defTermOrType → ctxt → tagged-val
bound-data (DefTerm pi v mtp t) Γ = to-string-tag "bound-value" Γ t
bound-data (DefType pi v k tp) Γ = to-string-tag "bound-value" Γ tp

-}

binder-data : ctxt → posinfo → var → (atk : tpkd) → erased? → maybe (if tk-is-type atk then term else type) → (from to : posinfo) → tagged-val
binder-data Γ pi x atk me val s e =
  strRunTag "binder" Γ $
  strAdd "symbol:" ≫str --strAdd "{\\\\\"symbol\\\\\":\\\\\"" ≫str
  strAdd x ≫str --strAdd "\\\\\"," ≫str
  atk-val atk val ≫str
  strAdd "§from:" ≫str --strAdd ",\\\\\"from\\\\\":" ≫str
  strAdd s ≫str
  strAdd "§to:" ≫str --strAdd ",\\\\\"to\\\\\":" ≫str
  strAdd e ≫str
  loc ≫str
  strErased?
  --strAdd "}"
  where
  loc : strM
  {-loc = maybe-else' (ctxt-get-info (qualif-var Γ x) Γ) strEmpty $ λ where
    (_ , fn , pi) →
      strAdd "§fn:" ≫str --strAdd ",\\\\\"fn\\\\\":\\\\\"" ≫str
      strAdd fn ≫str
      strAdd "§pos:" ≫str --strAdd "\\\\\",\\\\\"pos\\\\\":" ≫str
      strAdd pi-}
  loc = strAdd "§fn:" ≫str strAdd (ctxt-get-current-filename Γ) ≫str strAdd "§pos:" ≫str strAdd pi
  strErased? : strM
  strErased? =
    strAdd "§erased:" ≫str --strAdd ",\\\\\"erased\\\\\":" ≫str
    strAdd (if me then "true" else "false")
  val? : ∀ {ed} → maybe ⟦ ed ⟧ → strM
  val? = maybe-else strEmpty λ x →
    strAdd "§value:" ≫str --strAdd "\\\\\",\\\\\"value\\\\\":\\\\\"" ≫str
    to-stringe x
  atk-val : (atk : tpkd) → maybe (if tk-is-type atk then term else type) → strM
  atk-val (Tkt T) t? =
    strAdd "§type:" ≫str --strAdd "\\\\\"type\\\\\":\\\\\"" ≫str
    to-stringe T ≫str
    val? t? -- ≫str
    --strAdd "\\\\\""
  atk-val (Tkk k) T? =
    strAdd "§kind:" ≫str --strAdd "\\\\\"kind\\\\\":\\\\\"" ≫str
    to-stringe k ≫str
    val? T? -- ≫str
    --strAdd "\\\\\""

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
{-
keywords-data-var : erased? → tagged-val
keywords-data-var e =
  keywords ,  [[ if e then keyword-erased else keyword-noterased ]] , []
-}
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
  name = case Γ of λ where
    (mk-ctxt mod ss is (Δ , μ' , μ , η)) →
      if stringset-contains η (qualif-var Γ v')
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
                             [ var-location-data Γ x ] (just "This symbol was defined already.")

TpAppt-span : posinfo → posinfo → checking-mode → 𝕃 tagged-val → err-m → span
TpAppt-span pi pi' check tvs = mk-span "Application of a type to a term" pi pi' (checking-data check :: ll-data-type :: tvs)

TpApp-span : posinfo → posinfo → checking-mode → 𝕃 tagged-val → err-m → span
TpApp-span pi pi' check tvs = mk-span "Application of a type to a type" pi pi' (checking-data check :: ll-data-type :: tvs)

App-span : (is-locale : 𝔹) → posinfo → posinfo → checking-mode → 𝕃 tagged-val → err-m → span
App-span l pi pi' check tvs = mk-span "Application of a term to a term" pi pi' (checking-data check :: ll-data-term :: keywords-app-if-typed check l ++ tvs)

AppTp-span : posinfo → posinfo → checking-mode → 𝕃 tagged-val → err-m → span
AppTp-span pi pi' check tvs = mk-span "Application of a term to a type" pi pi' (checking-data check :: ll-data-term :: keywords-app-if-typed check ff ++ tvs)

TpQuant-span : ctxt → erased? → posinfo → posinfo → var → tpkd → ex-tp → checking-mode → 𝕃 tagged-val → err-m → span
TpQuant-span Γ me pi pi' x atk body check tvs err =
  let err-if-type-pi = maybe-if ( ~ (tk-is-type atk || me)) ≫maybe
                       just "Π-types must bind a term, not a type (use ∀ instead)"
      name = if me then "Implicit dependent function type" else "Dependent function type" in
  mk-span name pi (type-end-pos body) (checking-data check :: ll-data-type :: binder-data Γ pi' x atk me nothing (type-start-pos body) (type-end-pos body) :: tvs) (if isJust err-if-type-pi then err-if-type-pi else err)

TpLambda-span : ctxt → posinfo → posinfo → var → tpkd → ex-tp → checking-mode → 𝕃 tagged-val → err-m → span
TpLambda-span Γ pi pi' x atk body check tvs =
  mk-span "Type-level lambda abstraction" pi pi'
    (checking-data check :: ll-data-type :: binder-data Γ pi' x atk NotErased nothing (type-start-pos body) (type-end-pos body) :: tvs)

Iota-span : ctxt → posinfo → posinfo → var → type → ex-tp → checking-mode → 𝕃 tagged-val → err-m → span
Iota-span Γ pi pi' x t2 t2' check tvs = mk-span "Iota-abstraction" pi (type-end-pos t2') (explain "A dependent intersection type" :: checking-data check :: binder-data Γ pi' x (Tkt t2) ff nothing (type-start-pos t2') (type-end-pos t2') :: ll-data-type :: tvs)

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

erased-marg-span : ctxt → ex-tm → maybe type → span
erased-marg-span Γ t mtp = mk-span "Erased module parameter" (term-start-pos t) (term-end-pos t)
  (maybe-else [] (λ tp → [ type-data Γ tp ]) mtp)
  (just "An implicit module parameter variable occurs free in the erasure of the term.")

Lam-span-erased : erased? → string
Lam-span-erased Erased = "Erased lambda abstraction (term-level)"
Lam-span-erased NotErased = "Lambda abstraction (term-level)"

Lam-span : ctxt → checking-mode → posinfo → posinfo → erased? → var → tpkd → ex-tm → 𝕃 tagged-val → err-m → span
Lam-span Γ c pi pi' l x atk t tvs = mk-span (Lam-span-erased l) pi (term-end-pos t) 
                                           ((ll-data-term :: binder-data Γ pi' x atk l nothing (term-start-pos t) (term-end-pos t) :: checking-data c :: tvs)
                                           ++ bound-tp atk)
  where
  bound-tp : tpkd → 𝕃 tagged-val
  bound-tp (Tkt (TpHole _)) = []
  bound-tp atk = [ to-string-tag-tk "type of bound variable" Γ atk ]


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
                           (ll-data-term :: not-for-navigation :: [ explain "This term has not been type-checked."]) nothing-}

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
    (checking-data check :: ll-data-term :: expected-kind-if Γ k ++ tvs)
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
                                                   ^ " reduction." ) ])
  where side : left-right → string
        side Left = "the left-hand side"
        side Right = "the right-hand side"
        side Both = "both sides"
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
      ^ (if r then "" else "Do not ") ^ "Beta-reduce the type as we look for matches.") :: fst h)) (snd h)
  where h : 𝕃 tagged-val × err-m
        h = if isJust err
              then [] , err
              else if numrewrites =ℕ 0
                then [] , just "No rewrites could be performed."
                else [ strRunTag "Number of rewrites" empty-ctxt (strAdd $ ℕ-to-string numrewrites) ] , err

Phi-span : posinfo → posinfo → checking-mode → 𝕃 tagged-val → err-m → span
Phi-span pi pi' expected tvs = mk-span "Phi" pi pi' (checking-data expected :: ll-data-term :: tvs)

Chi-span : ctxt → posinfo → maybe type → ex-tm → checking-mode → 𝕃 tagged-val → err-m → span
Chi-span Γ pi m t' check tvs = mk-span "Chi" pi (term-end-pos t')  (ll-data-term :: checking-data check :: tvs ++ helper m)
  where helper : maybe type → 𝕃 tagged-val
        helper (just T) =  explain ("Check a term against an asserted type") :: [ to-string-tag "the asserted type" Γ T ]
        helper nothing = [ explain ("Change from checking mode (outside the term) to synthesizing (inside)") ] 

Sigma-span : posinfo → ex-tm → checking-mode → 𝕃 tagged-val → err-m → span
Sigma-span pi t check tvs =
  mk-span "Sigma" pi (term-end-pos t) 
     (ll-data-term :: checking-data check :: explain "Swap the sides of the equation synthesized for the body of this term" :: tvs)

Delta-span : posinfo → ex-tm → checking-mode → 𝕃 tagged-val → err-m → span
Delta-span pi t check tvs =
  mk-span "Delta" pi (term-end-pos t)
    (ll-data-term :: explain "Prove anything you want from a contradiction" :: checking-data check :: tvs)

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
        do-explain Abstract = [ explain ("Perform an elimination with the first term, after abstracting it from the expected type.") ]
        do-explain (AbstractVars vs) = [ strRunTag "explanation" Γ (strAdd "Perform an elimination with the first term, after abstracting the listed variables (" ≫str vars-to-string vs ≫str strAdd ") from the expected type.") ]
        do-explain AbstractEq = [ explain ("Perform an elimination with the first term, after abstracting it with an equation " 
                                         ^ "from the expected type.") ]

Mu-span : ctxt → posinfo → maybe var → posinfo → (motive? : maybe type) → checking-mode → 𝕃 tagged-val → err-m → span
Mu-span Γ pi x? pi' motive? check tvs = mk-span (if isJust x? then "Mu" else "Mu'") pi pi' (ll-data-term :: checking-data check :: explain ("Pattern match on a term" ^ (if isJust motive? then ", with a motive" else "")) :: tvs)

pattern-span : posinfo → var → 𝕃 ex-case-arg → span
pattern-span pi x as = mk-span "Pattern" pi (snd $ foldr (λ a r → if fst r then r else (tt , (case a of λ {(ExCaseArg me pi x) → posinfo-plus-str pi x}))) (ff , posinfo-plus-str pi x) as) [] nothing

pattern-clause-span : posinfo → ex-tm → span
pattern-clause-span pi t = mk-span "Pattern clause" pi (term-end-pos t) [] nothing

pattern-ctr-span : ctxt → posinfo → var → case-args → maybe type → err-m → span
pattern-ctr-span Γ pi x as tp =
  let x' = unqual-local x in
  mk-span "Pattern constructor" pi (posinfo-plus-str pi x') (checking-data synthesizing :: var-location-data Γ x :: ll-data-term :: symbol-data x' :: maybe-else' tp [] (λ tp → params-to-string-tag "args" Γ (rename-to-args empty-renamectxt as $ fst $ decompose-arrows Γ tp) :: []))
  where
  open import rename
  rename-to-args : renamectxt → case-args → params → params
  rename-to-args ρ (CaseArg e x :: as) (Param me x' atk :: ps) =
    Param me x (subst-renamectxt Γ ρ -tk atk) ::
      rename-to-args (renamectxt-insert ρ x' x) as ps
  rename-to-args ρ [] (Param me x atk :: ps) =
    Param me x (subst-renamectxt Γ ρ -tk atk) ::
      rename-to-args (renamectxt-insert ρ x x) [] ps
  rename-to-args ρ as ps = ps

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
  mk-span "Iota pair" pi pi' (explain "Inhabit a iota-type (dependent intersection type)." :: checking-data c :: ll-data-term :: tvs)

IotaProj-span : ex-tm → posinfo → checking-mode → 𝕃 tagged-val → err-m → span
IotaProj-span t pi' c tvs = mk-span "Iota projection" (term-start-pos t) pi' (checking-data c :: ll-data-term :: tvs)

Let-span : erased? → posinfo → posinfo → checking-mode → 𝕃 tagged-val → err-m → span
Let-span me pi pi' c tvs =
  mk-span (if me then "Erased Term Let" else "Term Let") pi pi' (ll-data-term :: checking-data c :: tvs)

TpLet-span : posinfo → posinfo → checking-mode → 𝕃 tagged-val → span
TpLet-span pi pi' c tvs =
  mk-span "Type Let" pi pi' (ll-data-type :: checking-data c :: tvs) nothing


