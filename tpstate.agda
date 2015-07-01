-- global type state, which is updated as we process definitions

module tpstate where

open import lib
open import cedille-types
open import rename
open import syntax-util

data tpstate : Set where
  mk-tpstate : string → -- output for the user

               trie term → -- untyped term definitions

               trie (term × type) → -- typed term definitions

               trie (type × kind) → -- kinded type definitions

               trie kind → -- kind definitions

               tpstate

add-untyped-term-def : var → term → tpstate → tpstate
add-untyped-term-def v trm (mk-tpstate o d td yd kd) = (mk-tpstate o (trie-insert d v trm) td yd kd)

add-typed-term-def : var → term → type → tpstate → tpstate
add-typed-term-def v trm tp (mk-tpstate o d td yd kd) = (mk-tpstate o d (trie-insert td v (trm , tp)) yd kd)

add-kinded-type-def : var → type → kind → tpstate → tpstate
add-kinded-type-def v tp knd (mk-tpstate o d td yd kd) = (mk-tpstate o d td (trie-insert yd v (tp , knd)) kd)

add-kind-def : var → kind → tpstate → tpstate
add-kind-def v knd (mk-tpstate o d td yd kd) = (mk-tpstate o d td yd (trie-insert kd v knd))

add-msg : string → tpstate → tpstate
add-msg m (mk-tpstate o d td yd kd) = mk-tpstate (o ^ m) d td yd kd

get-output-msg : tpstate → string
get-output-msg (mk-tpstate o _ _ _ _) = o

-- is the given string in the domain of any of the mappings in the typestate
in-dom-tpstate : tpstate → string → 𝔹
in-dom-tpstate (mk-tpstate _ d td yd kd) v = trie-contains d v || trie-contains td v || trie-contains yd v || trie-contains kd v

lookup-kind-var : tpstate → var → maybe kind
lookup-kind-var (mk-tpstate _ _ _ _ kd) v = trie-lookup kd v

lookup-type-var : tpstate → var → maybe type
lookup-type-var (mk-tpstate _ _ _ yd _) v with trie-lookup yd v
lookup-type-var (mk-tpstate _ _ _ yd _) v | nothing = nothing
lookup-type-var (mk-tpstate _ _ _ yd _) v | just (tp , knd) = just tp

lookup-type-var-k : tpstate → var → maybe kind
lookup-type-var-k (mk-tpstate _ _ _ yd _) v with trie-lookup yd v
lookup-type-var-k (mk-tpstate _ _ _ yd _) v | nothing = nothing
lookup-type-var-k (mk-tpstate _ _ _ yd _) v | just (tp , knd) = just knd

lookup-type-var-tk : tpstate → var → maybe (type × kind)
lookup-type-var-tk (mk-tpstate _ _ _ yd _) v = trie-lookup yd v

lookup-untyped-var : tpstate → var → maybe term
lookup-untyped-var (mk-tpstate _ d _ _ _) x = trie-lookup d x

-- untyped or typed
lookup-term-var : tpstate → var → maybe term
lookup-term-var s x with lookup-untyped-var s x 
lookup-term-var (mk-tpstate _ d td _ _) x | nothing with trie-lookup td x
lookup-term-var (mk-tpstate _ d td _ _) x | nothing | nothing = nothing
lookup-term-var (mk-tpstate _ d td _ _) x | nothing | just (trm , _) = just trm
lookup-term-var (mk-tpstate _ d td _ _) x | just trm = just trm

lookup-term-var-t : tpstate → var → maybe type
lookup-term-var-t (mk-tpstate _ _ td _ _) x with trie-lookup td x
lookup-term-var-t (mk-tpstate _ _ td _ _) x | nothing = nothing
lookup-term-var-t (mk-tpstate _ _ td _ _) x | just (trm , tp) = just tp

data tpstate-class : Set where
  tpstate-typing : term → type → tpstate-class
  tpstate-kinding : type → kind → tpstate-class
  tpstate-untyped : term → tpstate-class
  tpstate-superkinding : kind → tpstate-class
  tpstate-nothing : tpstate-class

lookup-var : tpstate → var → tpstate-class
lookup-var (mk-tpstate _ d td yd kd) x with trie-lookup td x
lookup-var (mk-tpstate _ d td yd kd) x | just (trm , tp) = tpstate-typing trm tp
lookup-var (mk-tpstate _ d td yd kd) x | nothing with trie-lookup d x
lookup-var (mk-tpstate _ d td yd kd) x | nothing | just trm = tpstate-untyped trm
lookup-var (mk-tpstate _ d td yd kd) x | nothing | nothing with trie-lookup yd x
lookup-var (mk-tpstate _ d td yd kd) x | nothing | nothing | just (tp , knd) = tpstate-kinding tp knd
lookup-var (mk-tpstate _ d td yd kd) x | nothing | nothing | nothing with trie-lookup kd x
lookup-var (mk-tpstate _ d td yd kd) x | nothing | nothing | nothing | just k = tpstate-superkinding k
lookup-var (mk-tpstate _ d td yd kd) x | nothing | nothing | nothing | nothing = tpstate-nothing

is-term-var : tpstate → var → 𝔹
is-term-var s v with lookup-term-var s v
is-term-var s v | nothing = ff
is-term-var s v | just _ = tt

tpstate-fresh-var : tpstate → (var → 𝔹) → string → renamectxt → string
tpstate-fresh-var s b v r = fresh-var v (λ x → b x || in-dom-tpstate s x) r

-- return tt iff the given var is defined at any level
is-defined : tpstate → var → 𝔹
is-defined (mk-tpstate _ d td yd kd) x = trie-contains d x || trie-contains td x || trie-contains yd x || trie-contains kd x

data evclass : Set where
  term-type : term → type → evclass
  type-kind : type → kind → evclass
  ev-ctorset : ctorset → evclass

-- local evidence context
evctxt : Set
evctxt = 𝕃 string × trie evclass

empty-evctxt : evctxt
empty-evctxt = [] , empty-trie

evctxt-insert : evctxt → string → evclass → evctxt
evctxt-insert (l , d) x c = (if trie-contains d x then l else x :: l) , trie-insert d x c

evctxt-lookup : evctxt → string → maybe evclass
evctxt-lookup (l , d) x = trie-lookup d x

evctxt-insert-tk : evctxt → string → string → tk → evctxt
evctxt-insert-tk Δ u x (Tkk k) = evctxt-insert Δ u (type-kind (TpVar x) k)
evctxt-insert-tk Δ u x (Tkt tp) = evctxt-insert Δ u (term-type (Var x) tp)

evctxt-insert-kinding : evctxt → string → type → kind → evctxt
evctxt-insert-kinding Δ u t k = evctxt-insert Δ u (type-kind t k)

evctxt-insert-typing : evctxt → string → term → type → evctxt
evctxt-insert-typing Δ u trm tp = evctxt-insert Δ u (term-type trm tp)

evctxt-insert-ctorset : evctxt → string → ctorset → evctxt
evctxt-insert-ctorset Δ u Θ = evctxt-insert Δ u (ev-ctorset Θ)

evclass-to-string : evclass → string
evclass-to-string (term-type trm tp) = term-to-string trm ^ " : " ^ type-to-string tp
evclass-to-string (type-kind tp knd) = type-to-string tp ^ " : " ^ kind-to-string knd
evclass-to-string (ev-ctorset Θ) = ctorset-to-string Θ

evctxt-to-string : evctxt → string
evctxt-to-string (l , d) = h (reverse l)
  where h : 𝕃 string → string
        h [] = "·"
        h (x :: l) with trie-lookup d x 
        h (x :: l) | nothing = "internal-error"
        h (x :: l) | just c =  x ^ " ∷ " ^ evclass-to-string c ^ " , " ^ h l

{- during type checking, we need to keep track of which term and type
   variables are bound.  Normally, this would be handled by the typing
   context, but here our evctxt will not do that. -}

bctxt : Set
bctxt = stringset

bctxt-add : bctxt → string → bctxt
bctxt-add = stringset-insert

bctxt-contains : bctxt → string → 𝔹
bctxt-contains b x = stringset-contains b x

empty-bctxt : bctxt
empty-bctxt = empty-trie

rename-pred : tpstate → bctxt → var → 𝔹
rename-pred s b v = is-defined s v || bctxt-contains b v

ctxt : Set
ctxt = evctxt × bctxt × renamectxt

empty-ctxt : ctxt
empty-ctxt = empty-evctxt , empty-bctxt , empty-renamectxt

show-evctxt-if : showCtxt → ctxt → string
show-evctxt-if showCtxtNo _ = ""
show-evctxt-if showCtxtYes (Δ , b , r) = evctxt-to-string Δ ^ " ⊢ "

rename-away : tpstate → bctxt → renamectxt → var → var
rename-away s b r x = rename-away-from x (rename-pred s b) r

rename-away' : tpstate → (var → 𝔹) → renamectxt → var → var
rename-away' s b r x = rename-away-from x (λ v → is-defined s v || b v) r


----------------------------------------------------------------------
-- the following are used in conversion.agda and check.agda
----------------------------------------------------------------------

{- the return type for all the check functions.  The returned string is
   information for the user about holes. -}
check-t : Set
check-t = error-t string

infixr 1 _≫check_ _≫synth_ _≫checksynth_ _≫synthcheck_ _≫conv_

synth-t : Set → Set
synth-t A = error-t (string × A)

conv-t : Set → Set
conv-t A = (maybe A) × string -- the string is for responses to holes or errors

_≫check_ : check-t → check-t → check-t
no-error x ≫check no-error x' = no-error (x ^ x')
no-error x ≫check yes-error x' = yes-error (x ^ x')
yes-error x ≫check no-error x' = yes-error (x ^ (newline-sep-if x x') ^ x')
yes-error x ≫check yes-error x' = yes-error (x ^ (newline-sep-if x x') ^ x')

_≫synth_ : {A B : Set} → synth-t A → (A → synth-t B) → synth-t B
no-error (m , a) ≫synth f with f a 
no-error (m , a) ≫synth f | no-error (m' , b) = no-error (m ^ m' , b)
no-error (m , a) ≫synth f | yes-error m' = yes-error (m ^ m')
yes-error x ≫synth f = yes-error x

_≫checksynth_ : check-t → {A : Set} → synth-t A → synth-t A
no-error x ≫checksynth no-error (x' , r) = no-error (x ^ x' , r)
no-error x ≫checksynth yes-error x' = yes-error (x ^ x')
yes-error x ≫checksynth no-error (x' , r) = yes-error (x ^ (newline-sep-if x x') ^ x')
yes-error x ≫checksynth yes-error x' = yes-error (x ^ (newline-sep-if x x') ^ x')

_≫synthcheck_ : {A : Set} → synth-t A → (A → check-t) → check-t
no-error (m , a) ≫synthcheck f with f a 
no-error (m , a) ≫synthcheck f | no-error m' = no-error (m ^ m')
no-error (m , a) ≫synthcheck f | yes-error m' = yes-error (m ^ m')
yes-error x ≫synthcheck f = yes-error x

_≫conv_ : {A B : Set} → conv-t A → (A → conv-t B) → conv-t B
nothing , m ≫conv f = nothing , m
just a , m ≫conv f with f a 
just a , m ≫conv f | r , m' = r , (m ^ (newline-sep-if m m') ^ m')

_≫checkconv_ : check-t → {A : Set} → conv-t A → conv-t A
(no-error x) ≫checkconv (r , x') = r , (x ^ (newline-sep-if x x') ^ x')
(yes-error x) ≫checkconv (r , x') = nothing , (x ^ (newline-sep-if x x') ^ x')

check-term-t : Set
check-term-t = tpstate → ctxt → evidence → term → type → check-t