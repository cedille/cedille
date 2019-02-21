import cedille-options
open import general-util
module spans (options : cedille-options.options) {mF : Set → Set} {{_ : monad mF}} where

open import lib
open import functions

open import cedille-types
open import constants 
open import conversion
open import ctxt
open import is-free
open import syntax-util
open import to-string options
open import subst
open import erase
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
print-file-id-table (mk-ctxt mod (syms , mn-fn , mn-ps , fn-ids , id , id-fns) is os Δ) =
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
spanM A = ctxt → spans → mF (A × ctxt × spans)

-- return for the spanM monad
spanMr : ∀{A : Set} → A → spanM A
spanMr a Γ ss = returnM (a , Γ , ss)

spanMok : spanM ⊤
spanMok = spanMr triv

get-ctxt : ∀{A : Set} → (ctxt → spanM A) → spanM A
get-ctxt m Γ ss = m Γ Γ ss

set-ctxt : ctxt → spanM ⊤
set-ctxt Γ _ ss = returnM (triv , Γ , ss)

get-error : ∀ {A : Set} → (maybe error-span → spanM A) → spanM A
get-error m Γ ss@(global-error _ _) = m nothing Γ ss
get-error m Γ ss@(regular-spans nothing _) = m nothing Γ ss
get-error m Γ ss@(regular-spans (just es) _) = m (just es) Γ ss

set-error : maybe (error-span) → spanM ⊤
set-error es Γ ss@(global-error _ _) = returnM (triv , Γ , ss)
set-error es Γ (regular-spans _ ss) = returnM (triv , Γ , regular-spans es ss)

restore-def : Set
restore-def = maybe qualif-info × maybe sym-info


spanM-set-params : params → spanM ⊤
spanM-set-params ps Γ ss = returnM (triv , (ctxt-params-def ps Γ) , ss)

-- this returns the previous ctxt-info, if any, for the given variable
spanM-push-term-decl : posinfo → var → type → spanM restore-def
spanM-push-term-decl pi x t Γ ss = let qi = ctxt-get-qi Γ x in returnM ((qi , qi ≫=maybe λ qi → ctxt-get-info (fst qi) Γ) , ctxt-term-decl pi x t Γ , ss)

-- let bindings currently cannot be made opaque, so this is OpacTrans. -tony
spanM-push-term-def : posinfo → var → term → type → spanM restore-def
spanM-push-term-def pi x t T Γ ss = let qi = ctxt-get-qi Γ x in returnM ((qi , qi ≫=maybe λ qi → ctxt-get-info (fst qi) Γ) , ctxt-term-def pi localScope OpacTrans x (just t) T Γ , ss)

spanM-push-term-udef : posinfo → var → term → spanM restore-def
spanM-push-term-udef pi x t Γ ss = let qi = ctxt-get-qi Γ x in returnM ((qi , qi ≫=maybe λ qi → ctxt-get-info (fst qi) Γ) , ctxt-term-udef pi localScope OpacTrans x t Γ , ss)
 
 -- return previous ctxt-info, if any
spanM-push-type-decl : posinfo → var → kind → spanM restore-def
spanM-push-type-decl pi x k Γ ss = let qi = ctxt-get-qi Γ x in returnM ((qi , qi ≫=maybe λ qi → ctxt-get-info (fst qi) Γ) , ctxt-type-decl pi x k Γ , ss)

spanM-push-type-def : posinfo → var → type → kind → spanM restore-def
spanM-push-type-def pi x t T Γ ss = let qi = ctxt-get-qi Γ x in returnM ((qi , qi ≫=maybe λ qi → ctxt-get-info (fst qi) Γ) , ctxt-type-def pi localScope OpacTrans x (just t) T Γ , ss)

spanM-lookup-restore-info : var → spanM restore-def
spanM-lookup-restore-info x =
  get-ctxt λ Γ →
  let qi = ctxt-get-qi Γ x in
  spanMr (qi , qi ≫=maybe λ qi → ctxt-get-info (fst qi) Γ)

-- returns the original sym-info.
-- clarification is idempotent: if the definition was already clarified,
-- then the operation succeeds, and returns (just sym-info).
-- this only returns nothing in the case that the opening didnt make sense:
-- you tried to open a term def, you tried to open an unknown def, etc...
-- basically any situation where the def wasnt a "proper" type def
spanM-clarify-def : opacity → var → spanM (maybe sym-info)
spanM-clarify-def o x Γ ss = returnM (result (ctxt-clarify-def Γ o x))
  where
  result : maybe (sym-info × ctxt) → (maybe sym-info × ctxt × spans)
  result (just (si , Γ')) = ( just si , Γ' , ss )
  result nothing = ( nothing , Γ , ss )

spanM-restore-clarified-def : var → sym-info → spanM ⊤
spanM-restore-clarified-def x si Γ ss = returnM (triv , ctxt-set-sym-info Γ x si , ss)

-- restore ctxt-info for the variable with given posinfo
spanM-restore-info : var → restore-def → spanM ⊤
spanM-restore-info v rd Γ ss = returnM (triv , ctxt-restore-info Γ v (fst rd) (snd rd) , ss)

_≫=span_ : ∀{A B : Set} → spanM A → (A → spanM B) → spanM B
(m₁ ≫=span m₂) ss Γ = m₁ ss Γ ≫=monad λ where (v , Γ , ss) → m₂ v Γ ss

_≫span_ : ∀{A B : Set} → spanM A → spanM B → spanM B
(m₁ ≫span m₂) = m₁ ≫=span (λ _ → m₂)

spanM-restore-info* : 𝕃 (var × restore-def) → spanM ⊤
spanM-restore-info* [] = spanMok
spanM-restore-info* ((v , qi , m) :: s) = spanM-restore-info v (qi , m) ≫span spanM-restore-info* s

infixl 2 _≫span_ _≫=span_ _≫=spanj_ _≫=spanm_ _≫=spanm'_ _≫=spanc_ _≫=spanc'_ _≫spanc_ _≫spanc'_

_≫=spanj_ : ∀{A : Set} → spanM (maybe A) → (A → spanM ⊤) → spanM ⊤
_≫=spanj_{A} m m' = m ≫=span cont
  where cont : maybe A → spanM ⊤
        cont nothing = spanMok
        cont (just x) = m' x


-- discard changes made by the first computation
_≫=spand_ : ∀{A B : Set} → spanM A → (A → spanM B) → spanM B
_≫=spand_{A} m m' Γ ss = m Γ ss ≫=monad λ where (v , _ , _) → m' v Γ ss

-- discard *spans* generated by first computation
_≫=spands_ : ∀ {A B : Set} → spanM A → (A → spanM B) → spanM B
_≫=spands_ m f Γ ss = m Γ ss ≫=monad λ where (v , Γ , _ ) → f v Γ ss

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
(m ≫=spanc m') Γ ss = m Γ ss ≫=monad λ where
  ((a , b) , Γ' , ss') → m' a b Γ' ss'

_≫=spanc'_ : ∀{A B C} → spanM (A × B) → (B → spanM C) → spanM C
(m ≫=spanc' m') Γ ss = m Γ ss ≫=monad λ where
  ((a , b) , Γ' , ss') → m' b Γ' ss'

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

with-ctxt : ∀ {A} → ctxt → spanM A → spanM A
with-ctxt Γ sm
  =   get-ctxt λ Γ' → set-ctxt Γ
    ≫span  sm
    ≫=span λ a → set-ctxt Γ'
    ≫span  spanMr a

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
spanM-add s Γ ss = returnM (triv , Γ , add-span s ss)

spanM-addl : 𝕃 span → spanM ⊤
spanM-addl [] = spanMok
spanM-addl (s :: ss) = spanM-add s ≫span spanM-addl ss

debug-span : posinfo → posinfo → 𝕃 tagged-val → span
debug-span pi pi' tvs = mk-span "Debug" pi pi' tvs nothing

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
location-data (file-name , pi) = strRunTag "location" empty-ctxt (strAdd file-name ≫str strAdd " - " ≫str strAdd pi)

var-location-data : ctxt → var → tagged-val
var-location-data Γ @ (mk-ctxt _ _ i _ _) x =
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

-- hnf-expected-type-if : ctxt → maybe type → 𝕃 tagged-val
-- hnf-expected-type-if Γ nothing = []
-- hnf-expected-type-if Γ (just tp) = [ hnf-expected-type Γ tp ]

type-data : ctxt → type → tagged-val
type-data = to-string-tag "type"

missing-type : tagged-val
missing-type = strRunTag "type" empty-ctxt $ strAdd "[undeclared]"

warning-data : string → tagged-val
warning-data = strRunTag "warning" empty-ctxt ∘ strAdd

check-for-type-mismatch : ctxt → string → type → type → 𝕃 tagged-val × err-m
check-for-type-mismatch Γ s tp tp' =
  let tp'' = hnf Γ unfold-head tp' tt in
  expected-type Γ tp :: [ type-data Γ tp' ] ,
  if conv-type Γ tp tp'' then nothing else just ("The expected type does not match the " ^ s ^ " type.")

check-for-type-mismatch-if : ctxt → string → maybe type → type → 𝕃 tagged-val × err-m
check-for-type-mismatch-if Γ s (just tp) = check-for-type-mismatch Γ s tp
check-for-type-mismatch-if Γ s nothing tp = [ type-data Γ tp ] , nothing

summary-data : {ed : exprd} → (name : string) → ctxt → ⟦ ed ⟧ → tagged-val
summary-data name Γ t = strRunTag "summary" Γ (strVar name ≫str strAdd " : " ≫str to-stringh t)

missing-kind : tagged-val
missing-kind = strRunTag "kind" empty-ctxt $ strAdd "[undeclared]"

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
arg-argument Γ (TermArg me x) = term-argument Γ x
arg-argument Γ (TypeArg x) = type-argument Γ x

kind-data : ctxt → kind → tagged-val
kind-data = to-string-tag "kind"

liftingType-data : ctxt → liftingType → tagged-val
liftingType-data = to-string-tag "lifting type"

kind-data-if : ctxt → maybe kind → 𝕃 tagged-val
kind-data-if Γ (just k) = [ kind-data Γ k ]
kind-data-if _ nothing = []

super-kind-data : tagged-val
super-kind-data = strRunTag "superkind" empty-ctxt $ strAdd "□"

symbol-data : string → tagged-val
symbol-data = strRunTag "symbol" empty-ctxt ∘ strAdd

tk-data : ctxt → tk → tagged-val
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

binder-data : ctxt → posinfo → var → (atk : tk) → maybeErased → maybe (if tk-is-type atk then term else type) → (from to : posinfo) → tagged-val
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
  erased?
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
  erased? : strM
  erased? =
    strAdd "§erased:" ≫str --strAdd ",\\\\\"erased\\\\\":" ≫str
    strAdd (if me then "true" else "false")
  val? : ∀ {ed} → maybe ⟦ ed ⟧ → strM
  val? = maybe-else strEmpty λ x →
    strAdd "§value:" ≫str --strAdd "\\\\\",\\\\\"value\\\\\":\\\\\"" ≫str
    to-stringh x
  atk-val : (atk : tk) → maybe (if tk-is-type atk then term else type) → strM
  atk-val (Tkt T) t? =
    strAdd "§type:" ≫str --strAdd "\\\\\"type\\\\\":\\\\\"" ≫str
    to-stringh T ≫str
    val? t? -- ≫str
    --strAdd "\\\\\""
  atk-val (Tkk k) T? =
    strAdd "§kind:" ≫str --strAdd "\\\\\"kind\\\\\":\\\\\"" ≫str
    to-stringh k ≫str
    val? T? -- ≫str
    --strAdd "\\\\\""

punctuation-data : tagged-val
punctuation-data = strRunTag "punctuation" empty-ctxt $ strAdd "true"

not-for-navigation : tagged-val
not-for-navigation = strRunTag "not-for-navigation" empty-ctxt $ strAdd "true"

is-erased : type → 𝔹
is-erased (TpVar _ _ ) = tt
is-erased _ = ff

keywords = "keywords"
--keyword-erased = "erased"
--keyword-noterased = "noterased"
keyword-application = "application"
keyword-locale = "meta-var-locale"

--noterased : tagged-val
--noterased = keywords , [[ keyword-noterased ]] , []

keywords-data : 𝕃 string → tagged-val
keywords-data kws = keywords , h kws , [] where
  h : 𝕃 string → rope
  h [] = [[]]
  h (k :: []) = [[ k ]]
  h (k :: ks) = [[ k ]] ⊹⊹ [[ " " ]] ⊹⊹ h ks
{-
keywords-data-var : maybeErased → tagged-val
keywords-data-var e =
  keywords ,  [[ if e then keyword-erased else keyword-noterased ]] , []
-}
keywords-app : (is-locale : 𝔹) → tagged-val
keywords-app l = keywords-data ([ keyword-application ] ++ (if l then [ keyword-locale ] else []))

keywords-app-if-typed : checking-mode → (is-locale : 𝔹) → 𝕃 tagged-val
keywords-app-if-typed untyped l = []
keywords-app-if-typed _ l = [ keywords-app l ]

error-if-not-eq : ctxt → type → 𝕃 tagged-val → 𝕃 tagged-val × err-m
error-if-not-eq Γ (TpEq pi t1 t2 pi') tvs = expected-type Γ (TpEq pi t1 t2 pi') :: tvs , nothing
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
  param : decl-class
  index : decl-class 

decl-class-name : decl-class → string
decl-class-name param = "parameter"
decl-class-name index = "index"

Decl-span : ctxt → decl-class → posinfo → posinfo → var → tk → maybeErased → posinfo → span
Decl-span Γ dc pi pi' v atk me pi'' = mk-span ((if tk-is-type atk then "Term " else "Type ") ^ (decl-class-name dc))
                                      pi pi'' [ binder-data Γ pi' v atk me nothing (tk-end-pos atk) pi'' ] nothing

TpVar-span : ctxt → posinfo → string → checking-mode → 𝕃 tagged-val → err-m → span
TpVar-span Γ pi v check tvs =
  mk-span name pi (posinfo-plus-str pi (unqual-local v))
    (checking-data check :: ll-data-type :: var-location-data Γ v :: symbol-data (unqual-local v) :: tvs)
  where
  v' = unqual-local v
  name = if isJust (data-lookup Γ (qualif-var Γ v') [])
           then "Datatype variable" else "Type variable"

Var-span : ctxt → posinfo → string → checking-mode → 𝕃 tagged-val → err-m → span
Var-span Γ pi v check tvs =
  mk-span name pi (posinfo-plus-str pi v')
    (checking-data check :: ll-data-term :: var-location-data Γ v :: symbol-data v' :: tvs)
  where
  v' = unqual-local v
  name : string
  name with qual-lookup Γ v'
  ...| just (_ , ctr-def _ _ _ _ _ , _) = "Constructor variable"
  ...| _ = "Term variable"

KndVar-span : ctxt → (posinfo × var) → (end-pi : posinfo) → params → checking-mode → 𝕃 tagged-val → err-m → span
KndVar-span Γ (pi , v) pi' ps check tvs =
  mk-span "Kind variable" pi pi'
    (checking-data check :: ll-data-kind :: var-location-data Γ v :: symbol-data (unqual-local v) :: super-kind-data :: (params-data Γ ps ++ tvs))

var-span-with-tags : maybeErased → ctxt → posinfo → string → checking-mode → tk → 𝕃 tagged-val → err-m → span
var-span-with-tags _ Γ pi x check (Tkk k) tags = TpVar-span Γ pi x check ({-keywords-data-var ff ::-} [ kind-data Γ k ] ++ tags)
var-span-with-tags e Γ pi x check (Tkt t) tags = Var-span Γ pi x check ({-keywords-data-var e ::-} [ type-data Γ t ] ++ tags)

var-span :  maybeErased → ctxt → posinfo → string → checking-mode → tk → err-m → span
var-span e Γ pi x check tk = var-span-with-tags e Γ pi x check tk []

redefined-var-span : ctxt → posinfo → var → span
redefined-var-span Γ pi x = mk-span "Variable definition" pi (posinfo-plus-str pi x)
                             [ var-location-data Γ x ] (just "This symbol was defined already.")

TpAppt-span : type → term → checking-mode → 𝕃 tagged-val → err-m → span
TpAppt-span tp t check tvs = mk-span "Application of a type to a term" (type-start-pos tp) (term-end-pos t) (checking-data check :: ll-data-type :: tvs)

TpApp-span : type → type → checking-mode → 𝕃 tagged-val → err-m → span
TpApp-span tp tp' check tvs = mk-span "Application of a type to a type" (type-start-pos tp) (type-end-pos tp') (checking-data check :: ll-data-type :: tvs)

App-span : (is-locale : 𝔹) → term → term → checking-mode → 𝕃 tagged-val → err-m → span
App-span l t t' check tvs = mk-span "Application of a term to a term" (term-start-pos t) (term-end-pos t') (checking-data check :: ll-data-term :: keywords-app-if-typed check l ++ tvs)

AppTp-span : term → type → checking-mode → 𝕃 tagged-val → err-m → span
AppTp-span t tp check tvs = mk-span "Application of a term to a type" (term-start-pos t) (type-end-pos tp) (checking-data check :: ll-data-term :: keywords-app-if-typed check ff ++ tvs)

TpQuant-e = 𝔹

is-pi : TpQuant-e
is-pi = tt

TpQuant-span : ctxt → TpQuant-e → posinfo → posinfo → var → tk → type → checking-mode → 𝕃 tagged-val → err-m → span
TpQuant-span Γ is-pi pi pi' x atk body check tvs err =
  let err-if-type-pi = if ~ tk-is-type atk && is-pi then just "Π-types must bind a term, not a type (use ∀ instead)" else nothing in
  mk-span (if is-pi then "Dependent function type" else "Implicit dependent function type")
       pi (type-end-pos body) (checking-data check :: ll-data-type :: binder-data Γ pi' x atk (~ is-pi) nothing (type-start-pos body) (type-end-pos body) :: tvs) (if isJust err-if-type-pi then err-if-type-pi else err)

TpLambda-span : ctxt → posinfo → posinfo → var → tk → type → checking-mode → 𝕃 tagged-val → err-m → span
TpLambda-span Γ pi pi' x atk body check tvs =
  mk-span "Type-level lambda abstraction" pi (type-end-pos body)
    (checking-data check :: ll-data-type :: binder-data Γ pi' x atk NotErased nothing (type-start-pos body) (type-end-pos body) :: tvs)

Iota-span : ctxt → posinfo → posinfo → var → type → checking-mode → 𝕃 tagged-val → err-m → span
Iota-span Γ pi pi' x t2 check tvs = mk-span "Iota-abstraction" pi (type-end-pos t2) (explain "A dependent intersection type" :: checking-data check :: binder-data Γ pi' x (Tkt t2) ff nothing (type-start-pos t2) (type-end-pos t2) :: ll-data-type :: tvs)

TpArrow-span : type → type → checking-mode → 𝕃 tagged-val → err-m → span
TpArrow-span t1 t2 check tvs = mk-span "Arrow type" (type-start-pos t1) (type-end-pos t2) (checking-data check :: ll-data-type :: tvs)

TpEq-span : posinfo → term → term → posinfo → checking-mode → 𝕃 tagged-val → err-m → span
TpEq-span pi t1 t2 pi' check tvs = mk-span "Equation" pi pi'
                             (explain "Equation between terms" :: checking-data check :: ll-data-type :: tvs)

Star-span : posinfo → checking-mode → err-m → span
Star-span pi check = mk-span Star-name pi (posinfo-plus pi 1) (checking-data check :: [ ll-data-kind ])

KndPi-span : ctxt → posinfo → posinfo → var → tk → kind → checking-mode → err-m → span
KndPi-span Γ pi pi' x atk k check =
  mk-span "Pi kind" pi (kind-end-pos k)
    (checking-data check :: ll-data-kind :: binder-data Γ pi' x atk ff nothing (kind-start-pos k) (kind-end-pos k) :: [ super-kind-data ])

KndArrow-span : kind → kind → checking-mode → err-m → span
KndArrow-span k k' check = mk-span "Arrow kind" (kind-start-pos k) (kind-end-pos k') (checking-data check :: ll-data-kind :: [ super-kind-data ])

KndTpArrow-span : type → kind → checking-mode → err-m → span
KndTpArrow-span t k check = mk-span "Arrow kind" (type-start-pos t) (kind-end-pos k) (checking-data check :: ll-data-kind :: [ super-kind-data ])

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
erasure Γ t = to-string-tag "erasure" Γ (erase-term t)

erased-marg-span : ctxt → term → maybe type → span
erased-marg-span Γ t mtp = mk-span "Erased module parameter" (term-start-pos t) (term-end-pos t)
  (maybe-else [] (λ tp → [ type-data Γ tp ]) mtp)
  (just "An implicit module parameter variable occurs free in the erasure of the term.")

Lam-span-erased : maybeErased → string
Lam-span-erased Erased = "Erased lambda abstraction (term-level)"
Lam-span-erased NotErased = "Lambda abstraction (term-level)"

Lam-span : ctxt → checking-mode → posinfo → posinfo → maybeErased → var → tk → term → 𝕃 tagged-val → err-m → span
Lam-span Γ c pi pi' NotErased x {-(SomeClass-} (Tkk k) {-)-} t tvs e =
  mk-span (Lam-span-erased NotErased) pi (term-end-pos t) (ll-data-term :: binder-data Γ pi' x (Tkk k) NotErased nothing (term-start-pos t) (term-end-pos t) :: checking-data c :: tvs) (e maybe-or just "λ-terms must bind a term, not a type (use Λ instead)")
--Lam-span Γ c pi l x NoClass t tvs = mk-span (Lam-span-erased l) pi (term-end-pos t) (ll-data-term :: binder-data Γ x :: checking-data c :: tvs)
Lam-span Γ c pi pi' l x {-(SomeClass-} atk {-)-} t tvs = mk-span (Lam-span-erased l) pi (term-end-pos t) 
                                           ((ll-data-term :: binder-data Γ pi' x atk l nothing (term-start-pos t) (term-end-pos t) :: checking-data c :: tvs)
                                           ++ bound-tp atk)
  where
  bound-tp : tk → 𝕃 tagged-val
  bound-tp (Tkt (TpHole _)) = []
  bound-tp atk = [ to-string-tag-tk "type of bound variable" Γ atk ]


compileFail-in : ctxt → term → 𝕃 tagged-val × err-m
compileFail-in Γ t with is-free-in check-erased compileFail-qual | qualif-term Γ t
...| is-free | tₒ with erase-term tₒ | hnf Γ unfold-all tₒ ff
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
    
CheckTerm-span : ctxt → (checked : checking-mode) → maybe type → term → posinfo → 𝕃 tagged-val → span
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
DefKind-span Γ pi x k pi' = mk-span "Kind-level definition" pi pi' (kind-data Γ k :: [ summary-data x Γ (Var pi "□") ]) nothing

DefDatatype-span : ctxt → posinfo → posinfo → var → params → (reg Mu bound : kind) → (mu : type) → (cast : type) → ctrs → posinfo → span
DefDatatype-span Γ pi pi' x ps k kₘᵤ kₓ Tₘᵤ Tₜₒ cs pi'' =
  mk-span "Datatype definition" pi pi'' (binder-data Γ pi' x (Tkk kₓ) ff nothing (kind-end-pos k) pi'' :: summary-data x Γ k :: summary-data (data-Is/ x) Γ kₘᵤ :: summary-data (data-is/ x) Γ Tₘᵤ :: summary-data (data-to/ x) Γ Tₜₒ :: to-string-tag (data-Is/ x) Γ kₘᵤ :: to-string-tag (data-is/ x) Γ Tₘᵤ :: to-string-tag (data-to/ x) Γ Tₜₒ :: []) nothing

{-unchecked-term-span : term → span
unchecked-term-span t = mk-span "Unchecked term" (term-start-pos t) (term-end-pos t)
                           (ll-data-term :: not-for-navigation :: [ explain "This term has not been type-checked."]) nothing-}

Beta-span : posinfo → posinfo → checking-mode → 𝕃 tagged-val → err-m → span
Beta-span pi pi' check tvs = mk-span "Beta axiom" pi pi'
                     (checking-data check :: ll-data-term :: explain "A term constant whose type states that β-equal terms are provably equal" :: tvs)

hole-span : ctxt → posinfo → maybe type → 𝕃 tagged-val → span
hole-span Γ pi tp tvs = 
  mk-span "Hole" pi (posinfo-plus pi 1)
    (ll-data-term :: expected-type-if Γ tp ++ tvs)
    (just "This hole remains to be filled in")

tp-hole-span : ctxt → posinfo → maybe kind → 𝕃 tagged-val → span
tp-hole-span Γ pi k tvs =
  mk-span "Hole" pi (posinfo-plus pi 1) 
    (ll-data-term :: expected-kind-if Γ k ++ tvs)
    (just "This hole remains to be filled in")


expected-to-string : checking-mode → string
expected-to-string checking = "expected"
expected-to-string synthesizing = "synthesized"
expected-to-string untyped = "untyped"

Epsilon-span : posinfo → leftRight → maybeMinus → term → checking-mode → 𝕃 tagged-val → err-m → span
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

optGuide-spans : optGuide → checking-mode → spanM ⊤
optGuide-spans NoGuide _ = spanMok
optGuide-spans (Guide pi x tp) expected =
  get-ctxt λ Γ → spanM-add (Var-span Γ pi x expected [] nothing)

Rho-span : posinfo → term → term → checking-mode → rhoHnf → ℕ ⊎ var → 𝕃 tagged-val → err-m → span
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

Chi-span : ctxt → posinfo → optType → term → checking-mode → 𝕃 tagged-val → err-m → span
Chi-span Γ pi m t' check tvs = mk-span "Chi" pi (term-end-pos t')  (ll-data-term :: checking-data check :: tvs ++ helper m)
  where helper : optType → 𝕃 tagged-val
        helper (SomeType T) =  explain ("Check a term against an asserted type") :: [ to-string-tag "the asserted type" Γ T ]
        helper NoType = [ explain ("Change from checking mode (outside the term) to synthesizing (inside)") ] 

Sigma-span : posinfo → term → checking-mode → 𝕃 tagged-val → err-m → span
Sigma-span pi t check tvs =
  mk-span "Sigma" pi (term-end-pos t) 
     (ll-data-term :: checking-data check :: explain "Swap the sides of the equation synthesized for the body of this term" :: tvs)

Delta-span : ctxt → posinfo → optType → term → checking-mode → 𝕃 tagged-val → err-m → span
Delta-span Γ pi T t check tvs =
  mk-span "Delta" pi (term-end-pos t)
    (ll-data-term :: explain "Prove anything you want from a contradiction" :: checking-data check :: tvs)

Open-span : ctxt → opacity → posinfo → var → term → checking-mode → 𝕃 tagged-val → err-m → span
Open-span Γ o pi x t check tvs =
  elim-pair (if o iff OpacTrans
    then ("Open" , "Open an opaque definition")
    else ("Close" , "Hide a definition")) λ name expl →
  mk-span name pi (term-end-pos t)
    (ll-data-term :: explain expl :: checking-data check :: tvs)

motive-label : string
motive-label = "the motive"

the-motive : ctxt → type → tagged-val
the-motive = to-string-tag motive-label

Theta-span : ctxt → posinfo → theta → term → lterms → checking-mode → 𝕃 tagged-val → err-m → span
Theta-span Γ pi u t ls check tvs = mk-span "Theta" pi (lterms-end-pos (term-end-pos t) ls) (ll-data-term :: checking-data check :: tvs ++ do-explain u)
  where do-explain : theta → 𝕃 tagged-val
        do-explain Abstract = [ explain ("Perform an elimination with the first term, after abstracting it from the expected type.") ]
        do-explain (AbstractVars vs) = [ strRunTag "explanation" Γ (strAdd "Perform an elimination with the first term, after abstracting the listed variables (" ≫str vars-to-string vs ≫str strAdd ") from the expected type.") ]
        do-explain AbstractEq = [ explain ("Perform an elimination with the first term, after abstracting it with an equation " 
                                         ^ "from the expected type.") ]

Mu-span : ctxt → posinfo → maybe var → posinfo → (motive? : maybe type) → checking-mode → 𝕃 tagged-val → err-m → span
Mu-span Γ pi x? pi' motive? check tvs = mk-span (if isJust x? then "Mu" else "Mu'") pi pi' (ll-data-term :: checking-data check :: explain ("Pattern match on a term" ^ (if isJust motive? then ", with a motive" else "")) :: tvs)

pattern-ctr-span : ctxt → posinfo → var → caseArgs → maybe type → err-m → span
pattern-ctr-span Γ pi x as tp =
  let x' = unqual-local x in
  mk-span "Pattern constructor" pi (posinfo-plus-str pi x') (checking-data synthesizing :: var-location-data Γ x :: ll-data-term :: symbol-data x' :: maybe-else' tp [] (λ tp → params-to-string-tag "args" Γ (rename-to-args empty-renamectxt as $ fst $ decompose-arrows Γ tp) :: []))
  where
  open import rename
  rename-to-args : renamectxt → caseArgs → params → params
  rename-to-args ρ (CaseTermArg _ _ x :: as) (Decl pi pi' me x' atk pi'' :: ps) =
    Decl pi pi' me x (subst-renamectxt Γ ρ atk) pi'' ::
      rename-to-args (renamectxt-insert ρ x' x) as ps
  rename-to-args ρ (CaseTypeArg _ x :: as) (Decl pi pi' me x' atk pi'' :: ps) =
    Decl pi pi' me x (subst-renamectxt Γ ρ atk) pi'' ::
      rename-to-args (renamectxt-insert ρ x' x) as ps
  rename-to-args ρ [] (Decl pi pi' me x atk pi'' :: ps) =
    Decl pi pi' me x (subst-renamectxt Γ ρ atk) pi'' ::
      rename-to-args (renamectxt-insert ρ x x) [] ps
  rename-to-args ρ as ps = ps

Lft-span : ctxt → posinfo → posinfo → var → term → checking-mode → 𝕃 tagged-val → err-m → span
Lft-span Γ pi pi' X t check tvs = mk-span "Lift type" pi (term-end-pos t) (checking-data check :: ll-data-type :: binder-data Γ pi' X (Tkk star) tt nothing (term-start-pos t) (term-end-pos t) :: tvs)

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

IotaProj-span : term → posinfo → checking-mode → 𝕃 tagged-val → err-m → span
IotaProj-span t pi' c tvs = mk-span "Iota projection" (term-start-pos t) pi' (checking-data c :: ll-data-term :: tvs)

-- <<<<<<< HEAD
Let-span : ctxt → checking-mode → posinfo → posinfo → forceErased → var → (atk : tk) → (if tk-is-type atk then term else type) → term → 𝕃 tagged-val → err-m → span
Let-span Γ c pi pi' fe x atk val t' tvs =
  mk-span name pi (term-end-pos t') (binder-data Γ pi' x atk ff (just val) (term-start-pos t') (term-end-pos t') :: ll-data-term :: checking-data c :: tvs)
  where name = if fe then "Erased Term Let" else "Term Let"
-- =======
-- Let-span : ctxt → checking-mode → posinfo → forceErased → defTermOrType → term → 𝕃 tagged-val → err-m → span
-- Let-span Γ c pi fe d t' tvs = mk-span name pi (term-end-pos t') (binder-data-const :: bound-data d Γ :: ll-data-term :: checking-data c :: tvs)
--   where name = if fe then "Erased Term Let" else "Term Let"
-- >>>>>>> master

TpLet-span : ctxt → checking-mode → posinfo → posinfo → var → (atk : tk) → (if tk-is-type atk then term else type) → type → 𝕃 tagged-val → err-m → span
TpLet-span Γ c pi pi' x atk val t' tvs =
  mk-span "Type Let" pi (type-end-pos t') (binder-data Γ pi' x atk ff (just val) (type-start-pos t') (type-end-pos t') :: ll-data-type :: checking-data c :: tvs)


