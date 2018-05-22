module syntax-util where

open import lib
open import cedille-types
open import general-util

posinfo-gen : posinfo
posinfo-gen = "generated"

first-position : posinfo
first-position = "1"

dummy-var : var
dummy-var = "_dummy"

id-term : term
id-term = Lam posinfo-gen KeptLambda posinfo-gen "x" NoClass (Var posinfo-gen "x")

compileFailType : type
compileFailType = Abs posinfo-gen All posinfo-gen "X" (Tkk (Star posinfo-gen))  (TpVar posinfo-gen "X")

delta-contra =
  let lambda x = Lam posinfo-gen KeptLambda posinfo-gen x NoClass in
  TpEq
    posinfo-gen
    (lambda "x" (lambda "y" (Var posinfo-gen "x")))
    (lambda "x" (lambda "y" (Var posinfo-gen "y")))
    posinfo-gen

qualif-info : Set
qualif-info = var × args

qualif : Set
qualif = trie qualif-info

tag : Set
tag = string × rope

tagged-val : Set
tagged-val = string × rope × 𝕃 tag

tags-to-rope : 𝕃 tag → rope
tags-to-rope [] = [[]]
tags-to-rope ((t , v) :: []) = [[ "\"" ^ t ^ "\":" ]] ⊹⊹ v
tags-to-rope ((t , v) :: ts) = [[ "\"" ^ t ^ "\":" ]] ⊹⊹ v ⊹⊹ [[ "," ]] ⊹⊹ tags-to-rope ts

-- We number these when so we can sort them back in emacs
tagged-val-to-rope : ℕ → tagged-val → rope
tagged-val-to-rope n (t , v , []) = [[ "\"" ^ t ^ "\":[\"" ^ ℕ-to-string n ^ "\",\"" ]] ⊹⊹ v ⊹⊹ [[ "\"]" ]]
tagged-val-to-rope n (t , v , tags) = [[ "\"" ^ t ^ "\":[\"" ^ ℕ-to-string n ^ "\",\"" ]] ⊹⊹ v ⊹⊹ [[ "\",{" ]] ⊹⊹ tags-to-rope tags ⊹⊹ [[ "}]" ]]

tagged-vals-to-rope : ℕ → 𝕃 tagged-val → rope
tagged-vals-to-rope n [] = [[]]
tagged-vals-to-rope n (s :: []) = tagged-val-to-rope n s
tagged-vals-to-rope n (s :: (s' :: ss)) = tagged-val-to-rope n s ⊹⊹ [[ "," ]] ⊹⊹ tagged-vals-to-rope (suc n) (s' :: ss)


make-tag : (name : string) → (values : 𝕃 tag) → (start : ℕ) → (end : ℕ) → tag
make-tag name vs start end = name , [[ "{\"start\":\"" ^ ℕ-to-string start ^ "\",\"end\":\"" ^ ℕ-to-string end ^ "\"" ]] ⊹⊹ vs-to-rope vs ⊹⊹ [[ "}" ]]
  where
    vs-to-rope : 𝕃 tag → rope
    vs-to-rope [] = [[]]
    vs-to-rope ((t , v) :: ts) = [[ ",\"" ^ t ^ "\":\"" ]] ⊹⊹ v ⊹⊹ [[ "\"" ]] ⊹⊹ vs-to-rope ts

posinfo-to-ℕ : posinfo → ℕ
posinfo-to-ℕ pi with string-to-ℕ pi
posinfo-to-ℕ pi | just n = n
posinfo-to-ℕ pi | nothing = 0 -- should not happen

posinfo-plus : posinfo → ℕ → posinfo
posinfo-plus pi n = ℕ-to-string (posinfo-to-ℕ pi + n)

posinfo-plus-str : posinfo → string → posinfo
posinfo-plus-str pi s = posinfo-plus pi (string-length s)

star : kind
star = Star posinfo-gen

-- qualify variable by module name
_#_ : string → string → string
fn # v = fn ^ "." ^  v

_%_ : posinfo → var → string
pi % v = pi ^ "@" ^ v

compileFail : var
compileFail = "compileFail"
compileFail-qual = "" % compileFail

mk-inst : params → args → trie arg × params
mk-inst (ParamsCons (Decl _ _ x _ _) ps) (ArgsCons a as) with mk-inst ps as
...| σ , ps' = trie-insert σ x a , ps'
mk-inst ps as = empty-trie , ps

apps-term : term → args → term
apps-term f (ArgsNil) = f
apps-term f (ArgsCons (TermArg t) as) = apps-term (App f NotErased t) as
apps-term f (ArgsCons (TypeArg t) as) = apps-term (AppTp f t) as

apps-type : type → args → type
apps-type f (ArgsNil) = f
apps-type f (ArgsCons (TermArg t) as) = apps-type (TpAppt f t) as
apps-type f (ArgsCons (TypeArg t) as) = apps-type (TpApp f t) as

append-params : params → params → params
append-params (ParamsCons p ps) qs = ParamsCons p (append-params ps qs)
append-params ParamsNil qs = qs

append-args : args → args → args
append-args (ArgsCons p ps) qs = ArgsCons p (append-args ps qs)
append-args (ArgsNil) qs = qs

qualif-lookup-term : posinfo → qualif → string → term
qualif-lookup-term pi σ x with trie-lookup σ x
... | just (x' , as) = apps-term (Var pi x') as
... | _ = Var pi x

qualif-lookup-type : posinfo → qualif → string → type
qualif-lookup-type pi σ x with trie-lookup σ x
... | just (x' , as) = apps-type (TpVar pi x') as
... | _ = TpVar pi x

qualif-lookup-kind : posinfo → args → qualif → string → kind
qualif-lookup-kind pi xs σ x with trie-lookup σ x
... | just (x' , as) = KndVar pi x' (append-args as xs)
... | _ = KndVar pi x xs

inst-lookup-term : posinfo → trie arg → string → term
inst-lookup-term pi σ x with trie-lookup σ x
... | just (TermArg t) = t
... | _ = Var pi x

inst-lookup-type : posinfo → trie arg → string → type
inst-lookup-type pi σ x with trie-lookup σ x
... | just (TypeArg t) = t
... | _ = TpVar pi x

params-to-args : params → args
params-to-args ParamsNil = ArgsNil
params-to-args (ParamsCons (Decl _ p v (Tkt t) _) ps) = ArgsCons (TermArg (Var p v)) (params-to-args ps)
params-to-args (ParamsCons (Decl _ p v (Tkk k) _) ps) = ArgsCons (TypeArg (TpVar p v)) (params-to-args ps)

qualif-insert-params : qualif → var → var → params → qualif
qualif-insert-params σ qv v ps = trie-insert σ v (qv , params-to-args ps)

qualif-insert-import : qualif → var → optAs → 𝕃 string → args → qualif
qualif-insert-import σ mn oa [] as = σ
qualif-insert-import σ mn oa (v :: vs) as = qualif-insert-import (trie-insert σ (import-as v oa) (mn # v , as)) mn oa vs as
  where
  import-as : var → optAs → var
  import-as v NoOptAs = v
  import-as v (SomeOptAs pi pfx) = pfx # v

tk-is-type : tk → 𝔹
tk-is-type (Tkt _) = tt
tk-is-type (Tkk _) = ff

binder-is-pi : binder → 𝔹
binder-is-pi Pi = tt
binder-is-pi _ = ff

lam-is-erased : lam → 𝔹
lam-is-erased ErasedLambda = tt
lam-is-erased _ = ff

term-start-pos : term → posinfo
type-start-pos : type → posinfo
kind-start-pos : kind → posinfo
liftingType-start-pos : liftingType → posinfo

term-start-pos (App t x t₁) = term-start-pos t
term-start-pos (AppTp t tp) = term-start-pos t
term-start-pos (Hole pi) = pi
term-start-pos (Lam pi x _ x₁ x₂ t) = pi
term-start-pos (Let pi _ _) = pi
term-start-pos (Parens pi t pi') = pi
term-start-pos (Var pi x₁) = pi
term-start-pos (Beta pi _ _) = pi
term-start-pos (IotaPair pi _ _ _ _) = pi
term-start-pos (IotaProj t _ _) = term-start-pos t
term-start-pos (Epsilon pi _ _ _) = pi
term-start-pos (Phi pi _ _ _ _) = pi
term-start-pos (Rho pi _ _ _ _ _) = pi
term-start-pos (Chi pi _ _) = pi
term-start-pos (Delta pi _ _) = pi
term-start-pos (Sigma pi _) = pi
term-start-pos (Theta pi _ _ _) = pi

type-start-pos (Abs pi _ _ _ _ _) = pi
type-start-pos (TpLambda pi _ _ _ _) = pi
type-start-pos (Iota pi _ _ _ _) = pi
type-start-pos (Lft pi _ _ _ _) = pi
type-start-pos (TpApp t t₁) = type-start-pos t
type-start-pos (TpAppt t x) = type-start-pos t
type-start-pos (TpArrow t _ t₁) = type-start-pos t
type-start-pos (TpEq pi _ _ pi') = pi
type-start-pos (TpParens pi _ pi') = pi
type-start-pos (TpVar pi x₁) = pi
type-start-pos (NoSpans t _) = type-start-pos t -- we are not expecting this on input
type-start-pos (TpHole pi) = pi --ACG

kind-start-pos (KndArrow k k₁) = kind-start-pos k
kind-start-pos (KndParens pi k pi') = pi
kind-start-pos (KndPi pi _ x x₁ k) = pi
kind-start-pos (KndTpArrow x k) = type-start-pos x
kind-start-pos (KndVar pi x₁ _) = pi
kind-start-pos (Star pi) = pi

liftingType-start-pos (LiftArrow l l') = liftingType-start-pos l
liftingType-start-pos (LiftParens pi l pi') = pi
liftingType-start-pos (LiftPi pi x₁ x₂ l) = pi
liftingType-start-pos (LiftStar pi) = pi
liftingType-start-pos (LiftTpArrow t l) = type-start-pos t

term-end-pos : term → posinfo
type-end-pos : type → posinfo
kind-end-pos : kind → posinfo
liftingType-end-pos : liftingType → posinfo
tk-end-pos : tk → posinfo
lterms-end-pos : lterms → posinfo
args-end-pos : (if-nil : posinfo) → args → posinfo
arg-end-pos : arg → posinfo
kvar-end-pos : posinfo → var → args → posinfo

term-end-pos (App t x t') = term-end-pos t'
term-end-pos (AppTp t tp) = type-end-pos tp
term-end-pos (Hole pi) = posinfo-plus pi 1
term-end-pos (Lam pi x _ x₁ x₂ t) = term-end-pos t
term-end-pos (Let _ _ t) = term-end-pos t
term-end-pos (Parens pi t pi') = pi'
term-end-pos (Var pi x) = posinfo-plus-str pi x
term-end-pos (Beta pi _ (SomeTerm t pi')) = pi'
term-end-pos (Beta pi (SomeTerm t pi') _) = pi'
term-end-pos (Beta pi NoTerm NoTerm) = posinfo-plus pi 1
term-end-pos (IotaPair _ _ _ _ pi) = pi
term-end-pos (IotaProj _ _ pi) = pi
term-end-pos (Epsilon pi _ _ t) = term-end-pos t
term-end-pos (Phi _ _ _ _ pi) = pi
term-end-pos (Rho pi _ _ _ t t') = term-end-pos t'
term-end-pos (Chi pi T t') = term-end-pos t'
term-end-pos (Delta pi oT t) = term-end-pos t
term-end-pos (Sigma pi t) = term-end-pos t
term-end-pos (Theta _ _ _ ls) = lterms-end-pos ls

type-end-pos (Abs pi _ _ _ _ t) = type-end-pos t
type-end-pos (TpLambda _ _ _ _ t) = type-end-pos t
type-end-pos (Iota _ _ _ _ tp) = type-end-pos tp
type-end-pos (Lft pi _ _ _ t) = liftingType-end-pos t
type-end-pos (TpApp t t') = type-end-pos t'
type-end-pos (TpAppt t x) = term-end-pos x
type-end-pos (TpArrow t _ t') = type-end-pos t'
type-end-pos (TpEq pi _ _ pi') = pi'
type-end-pos (TpParens pi _ pi') = pi'
type-end-pos (TpVar pi x) = posinfo-plus-str pi x
type-end-pos (TpHole pi) = posinfo-plus pi 1
type-end-pos (NoSpans t pi) = pi

kind-end-pos (KndArrow k k') = kind-end-pos k'
kind-end-pos (KndParens pi k pi') = pi'
kind-end-pos (KndPi pi _ x x₁ k) = kind-end-pos k
kind-end-pos (KndTpArrow x k) = kind-end-pos k
kind-end-pos (KndVar pi x ys) = args-end-pos (posinfo-plus-str pi x) ys
kind-end-pos (Star pi) = posinfo-plus pi 1

tk-end-pos (Tkt T) = type-end-pos T
tk-end-pos (Tkk k) = kind-end-pos k

args-end-pos pi (ArgsCons x ys) = args-end-pos (arg-end-pos x) ys
args-end-pos pi ArgsNil = pi

arg-end-pos (TermArg t) = term-end-pos t
arg-end-pos (TypeArg T) = type-end-pos T

kvar-end-pos pi v = args-end-pos (posinfo-plus-str pi v)

liftingType-end-pos (LiftArrow l l') = liftingType-end-pos l'
liftingType-end-pos (LiftParens pi l pi') = pi'
liftingType-end-pos (LiftPi x x₁ x₂ l) = liftingType-end-pos l
liftingType-end-pos (LiftStar pi) = posinfo-plus pi 1
liftingType-end-pos (LiftTpArrow x l) = liftingType-end-pos l

lterms-end-pos (LtermsNil pi) = posinfo-plus pi 1 -- must add one for the implicit Beta that we will add at the end
lterms-end-pos (LtermsCons _ _ ls) = lterms-end-pos ls

{- return the end position of the given term if it is there, otherwise
   the given posinfo -}
optTerm-end-pos : posinfo → optTerm → posinfo
optTerm-end-pos pi NoTerm = pi
optTerm-end-pos pi (SomeTerm x x₁) = x₁

optTerm-end-pos-beta : posinfo → optTerm → optTerm → posinfo
optTerm-end-pos-beta pi _ (SomeTerm x pi') = pi'
optTerm-end-pos-beta pi (SomeTerm x pi') NoTerm = pi'
optTerm-end-pos-beta pi NoTerm NoTerm = posinfo-plus pi 1

optAs-or : optAs → posinfo → var → posinfo × var
optAs-or NoOptAs pi x = pi , x
optAs-or (SomeOptAs pi x) _ _ = pi , x

tk-arrow-kind : tk → kind → kind
tk-arrow-kind (Tkk k) k' = KndArrow k k'
tk-arrow-kind (Tkt t) k = KndTpArrow t k

TpApp-tk : type → var → tk → type
TpApp-tk tp x (Tkk _) = TpApp tp (TpVar posinfo-gen x)
TpApp-tk tp x (Tkt _) = TpAppt tp (Var posinfo-gen x)

-- expression descriptor
data exprd : Set where
  TERM : exprd
  TYPE : exprd
  KIND : exprd
  LIFTINGTYPE : exprd
  TK : exprd
  ARG : exprd
  QUALIF : exprd

⟦_⟧ : exprd → Set
⟦ TERM ⟧ = term
⟦ TYPE ⟧ = type
⟦ KIND ⟧ = kind
⟦ LIFTINGTYPE ⟧ = liftingType
⟦ TK ⟧ = tk
⟦ ARG ⟧ = arg
⟦ QUALIF ⟧ = qualif-info

exprd-name : exprd → string
exprd-name TERM = "term"
exprd-name TYPE = "type"
exprd-name KIND = "kind"
exprd-name LIFTINGTYPE = "lifting type"
exprd-name TK = "type-kind"
exprd-name ARG = "argument"
exprd-name QUALIF = "qualification"

-- checking-sythesizing enum
data checking-mode : Set where
  checking : checking-mode
  synthesizing : checking-mode
  untyped : checking-mode

maybe-to-checking : {A : Set} → maybe A → checking-mode
maybe-to-checking (just _) = checking
maybe-to-checking nothing = synthesizing

is-app : {ed : exprd} → ⟦ ed ⟧ → 𝔹
is-app{TERM} (App _ _ _) = tt
is-app{TERM} (AppTp _ _) = tt
is-app{TYPE} (TpApp _ _) = tt
is-app{TYPE} (TpAppt _ _) = tt
is-app _ = ff

is-arrow : {ed : exprd} → ⟦ ed ⟧ → 𝔹
is-arrow{TYPE} (TpArrow _ _ _) = tt
is-arrow{KIND} (KndTpArrow _ _) = tt
is-arrow{KIND} (KndArrow _ _) = tt
is-arrow{LIFTINGTYPE} (LiftArrow _ _) = tt
is-arrow{LIFTINGTYPE} (LiftTpArrow _ _) = tt
is-arrow _ = ff

is-abs : {ed : exprd} → ⟦ ed ⟧ → 𝔹
is-abs{TERM} (Let _ _ _) = tt
is-abs{TERM} (Lam _ _ _ _ _ _) = tt
is-abs{TYPE} (Abs _ _ _ _ _ _) = tt
is-abs{TYPE} (TpLambda _ _ _ _ _) = tt
is-abs{TYPE} (Iota _ _ _ _ _) = tt
is-abs{KIND} (KndPi _ _ _ _ _) = tt
is-abs{LIFTINGTYPE} (LiftPi _ _ _ _) = tt
is-abs _ = ff

is-eq-op : {ed : exprd} → ⟦ ed ⟧ → 𝔹
is-eq-op{TERM} (Sigma _ _) = tt
is-eq-op{TERM} (Epsilon _ _ _ _) = tt
is-eq-op{TERM} (Rho _ _ _ _ _ _) = tt
is-eq-op{TERM} (Chi _ _ _) = tt
is-eq-op{TERM} (Phi _ _ _ _ _) = tt
is-eq-op _ = ff

is-beta : {ed : exprd} → ⟦ ed ⟧ → 𝔹
is-beta{TERM} (Beta _ _ _) = tt
is-beta _ = ff

eq-maybeErased : maybeErased → maybeErased → 𝔹
eq-maybeErased Erased Erased = tt
eq-maybeErased Erased NotErased = ff
eq-maybeErased NotErased Erased = ff
eq-maybeErased NotErased NotErased = tt

eq-lam : lam → lam → 𝔹
eq-lam ErasedLambda ErasedLambda = tt
eq-lam ErasedLambda KeptLambda = ff
eq-lam KeptLambda ErasedLambda = ff
eq-lam KeptLambda KeptLambda = tt

eq-binder : binder → binder → 𝔹
eq-binder All All = tt
eq-binder Pi Pi = tt
eq-binder _ _ = ff

eq-arrowtype : arrowtype → arrowtype → 𝔹
eq-arrowtype ErasedArrow ErasedArrow = tt
eq-arrowtype UnerasedArrow UnerasedArrow = tt
eq-arrowtype _ _ = ff

arrowtype-matches-binder : arrowtype → binder → 𝔹
arrowtype-matches-binder ErasedArrow All = tt
arrowtype-matches-binder UnerasedArrow Pi = tt
arrowtype-matches-binder _ _ = ff

optPublic-is-public : optPublic → 𝔹
optPublic-is-public IsPublic = tt
optPublic-is-public NotPublic = ff

------------------------------------------------------
-- functions intended for building terms for testing
------------------------------------------------------
mlam : var → term → term
mlam x t = Lam posinfo-gen KeptLambda posinfo-gen x NoClass t

Mlam : var → term → term
Mlam x t = Lam posinfo-gen ErasedLambda posinfo-gen x NoClass t

mappe : term → term → term
mappe t1 t2 = App t1 Erased t2

mapp : term → term → term
mapp t1 t2 = App t1 NotErased t2

mvar : var → term
mvar x = Var posinfo-gen x

mtpvar : var → type
mtpvar x = TpVar posinfo-gen x

mall : var → tk → type → type
mall x tk tp = Abs posinfo-gen All posinfo-gen x tk tp

mtplam : var → tk → type → type
mtplam x tk tp = TpLambda posinfo-gen posinfo-gen x tk tp

{- strip off lambda-abstractions from the term, return the lambda-bound vars and the innermost body.
   The intention is to call this with at least the erasure of a term, if not the hnf -- so we do
   not check for parens, etc. -}
decompose-lams : term → (𝕃 var) × term
decompose-lams (Lam _ _ _ x _ t) with decompose-lams t
decompose-lams (Lam _ _ _ x _ t) | vs , body = (x :: vs) , body
decompose-lams t = [] , t

{- decompose a term into spine form consisting of a non-applications head and arguments.
   The outer arguments will come earlier in the list than the inner ones.
   As for decompose-lams, we assume the term is at least erased. -}
decompose-apps : term → term × (𝕃 term)
decompose-apps (App t _ t') with decompose-apps t
decompose-apps (App t _ t') | h , args = h , (t' :: args)
decompose-apps t = t , []

decompose-var-headed : (var → 𝔹) → term → maybe (var × (𝕃 term))
decompose-var-headed is-bound t with decompose-apps t
decompose-var-headed is-bound t | Var _ x , args = if is-bound x then nothing else (just (x , args))
decompose-var-headed is-bound t | _ = nothing

data tty : Set where
  tterm : term → tty
  ttype : type → tty

decompose-tpapps : type → type × 𝕃 tty 
decompose-tpapps (TpApp t t') with decompose-tpapps t
decompose-tpapps (TpApp t t') | h , args = h , (ttype t') :: args
decompose-tpapps (TpAppt t t') with decompose-tpapps t
decompose-tpapps (TpAppt t t') | h , args = h , (tterm t') :: args
decompose-tpapps (TpParens _ t _) = decompose-tpapps t
decompose-tpapps t = t , []

recompose-tpapps : type × 𝕃 tty → type
recompose-tpapps (h , []) = h
recompose-tpapps (h , ((tterm t') :: args)) = TpAppt (recompose-tpapps (h , args)) t'
recompose-tpapps (h , ((ttype t') :: args)) = TpApp (recompose-tpapps (h , args)) t'

vars-to-𝕃 : vars → 𝕃 var
vars-to-𝕃 (VarsStart v) = [ v ]
vars-to-𝕃 (VarsNext v vs) = v :: vars-to-𝕃 vs

{- lambda-abstract the input variables in reverse order around the
   given term (so closest to the top of the list is bound deepest in
   the resulting term). -}
Lam* : 𝕃 var → term → term
Lam* [] t = t
Lam* (x :: xs) t = Lam* xs (Lam posinfo-gen KeptLambda posinfo-gen x NoClass t)

App* : term → 𝕃 (maybeErased × term) → term
App* t [] = t
App* t ((m , arg) :: args) = App (App* t args) m arg

App*' : term → 𝕃 term → term
App*' t [] = t
App*' t (arg :: args) = App*' (App t NotErased arg) args

TpApp* : type → 𝕃 type → type
TpApp* t [] = t
TpApp* t (arg :: args) = (TpApp (TpApp* t args) arg)

LiftArrow* : 𝕃 liftingType → liftingType → liftingType
LiftArrow* [] l = l
LiftArrow* (l' :: ls) l = LiftArrow* ls (LiftArrow l' l)

is-intro-form : term → 𝔹
is-intro-form (Lam _ _ _ _ _ _) = tt
--is-intro-form (IotaPair _ _ _ _ _) = tt
is-intro-form _ = ff

erase : { ed : exprd } → ⟦ ed ⟧ → ⟦ ed ⟧
erase-term : term → term
erase-type : type → type
erase-kind : kind → kind
erase-lterms : theta → lterms → 𝕃 term
erase-tk : tk → tk
-- erase-optType : optType → optType
erase-liftingType : liftingType → liftingType

erase-if : 𝔹 → { ed : exprd } → ⟦ ed ⟧ → ⟦ ed ⟧
erase-if tt = erase
erase-if ff = id

erase-term (Parens _ t _) = erase-term t
erase-term (App t1 Erased t2) = erase-term t1
erase-term (App t1 NotErased t2) = App (erase-term t1) NotErased (erase-term t2)
erase-term (AppTp t tp) = erase-term t
erase-term (Lam _ ErasedLambda _ _ _ t) = erase-term t
erase-term (Let pi (DefTerm pi'' x _ t) t') = Let pi (DefTerm pi'' x NoCheckType (erase-term t)) (erase-term t')
erase-term (Let _ (DefType _ _ _ _) t) = erase-term t
erase-term (Lam pi KeptLambda pi' x oc t) = Lam pi KeptLambda pi' x NoClass (erase-term t)
erase-term (Var pi x) = Var pi x
erase-term (Beta pi _ NoTerm) = id-term
erase-term (Beta pi _ (SomeTerm t _)) = erase-term t
erase-term (IotaPair pi t1 t2 _ pi') = erase-term t1
erase-term (IotaProj t n pi) = erase-term t
erase-term (Epsilon pi lr _ t) = erase-term t
erase-term (Sigma pi t) = erase-term t
erase-term (Hole pi) = Hole pi
erase-term (Phi pi t t₁ t₂ pi') = erase-term t₂
erase-term (Rho pi _ _ t _ t') = erase-term t'
erase-term (Chi pi T t') = erase-term t'
erase-term (Delta pi T t) = erase-term t
erase-term (Theta pi u t ls) = App*' (erase-term t) (erase-lterms u ls)

-- Only erases TERMS in types, leaving the structure of types the same
erase-type (Abs pi b pi' v t-k tp) = Abs pi b pi' v (erase-tk t-k) (erase-type tp)
erase-type (Iota pi pi' v otp tp) = Iota pi pi' v (erase-type otp) (erase-type tp)
erase-type (Lft pi pi' v t lt) = Lft pi pi' v (erase-term t) (erase-liftingType lt)
erase-type (NoSpans tp pi) = NoSpans (erase-type tp) pi
erase-type (TpApp tp tp') = TpApp (erase-type tp) (erase-type tp')
erase-type (TpAppt tp t) = TpAppt (erase-type tp) (erase-term t)
erase-type (TpArrow tp at tp') = TpArrow (erase-type tp) at (erase-type tp')
erase-type (TpEq pi t t' pi') = TpEq pi (erase-term t) (erase-term t') pi'
erase-type (TpLambda pi pi' v t-k tp) = TpLambda pi pi' v (erase-tk t-k) (erase-type tp)
erase-type (TpParens pi tp pi') = TpParens pi (erase-type tp) pi'
erase-type (TpHole pi) = TpHole pi
erase-type (TpVar pi x) = TpVar pi x

-- Only erases TERMS in types in kinds, leaving the structure of kinds and types in those kinds the same
erase-kind (KndArrow k k') = KndArrow (erase-kind k) (erase-kind k')
erase-kind (KndParens pi k pi') = KndParens pi (erase-kind k) pi'
erase-kind (KndPi pi pi' v t-k k) = KndPi pi pi' v (erase-tk t-k) (erase-kind k)
erase-kind (KndTpArrow tp k) = KndTpArrow (erase-type tp) (erase-kind k)
erase-kind (KndVar pi x ps) = KndVar pi x ps
erase-kind (Star pi) = Star pi

erase{TERM} t = erase-term t
erase{TYPE} tp = erase-type tp
erase{KIND} k = erase-kind k
erase{LIFTINGTYPE} lt = erase-liftingType lt
erase{TK} atk = erase-tk atk
erase{ARG} a = a
erase{QUALIF} q = q

erase-tk (Tkt tp) = Tkt (erase-type tp)
erase-tk (Tkk k) = Tkk (erase-kind k)

-- erase-optType (SomeType tp) = SomeType (erase-type tp)
-- erase-optType NoType = NoType

erase-liftingType (LiftArrow lt lt') = LiftArrow (erase-liftingType lt) (erase-liftingType lt')
erase-liftingType (LiftParens pi lt pi') = LiftParens pi (erase-liftingType lt) pi'
erase-liftingType (LiftPi pi v tp lt) = LiftPi pi v (erase-type tp) (erase-liftingType lt)
erase-liftingType (LiftTpArrow tp lt) = LiftTpArrow (erase-type tp) (erase-liftingType lt)
erase-liftingType lt = lt

erase-lterms Abstract (LtermsNil _) = []
erase-lterms (AbstractVars _) (LtermsNil _) = []
erase-lterms AbstractEq (LtermsNil pi) = [ Beta pi NoTerm NoTerm ]
erase-lterms u (LtermsCons NotErased t ls) = (erase-term t) :: erase-lterms u ls
erase-lterms u (LtermsCons Erased t ls) = erase-lterms u ls

lterms-to-𝕃h : theta → lterms → 𝕃 (maybeErased × term)
lterms-to-𝕃h Abstract (LtermsNil _) = []
lterms-to-𝕃h (AbstractVars _) (LtermsNil _) = []
lterms-to-𝕃h AbstractEq (LtermsNil pi) = [ NotErased , Beta pi NoTerm NoTerm ]
lterms-to-𝕃h u (LtermsCons m t ls) = (m , t) :: (lterms-to-𝕃h u ls)

lterms-to-𝕃 : theta → lterms → 𝕃 (maybeErased × term)
lterms-to-𝕃 u ls = reverse (lterms-to-𝕃h u ls)

lterms-to-𝕃' : theta → lterms → 𝕃 term
lterms-to-𝕃' u ls = map snd (lterms-to-𝕃 u ls)

erase-lterms-if : 𝔹 → theta → lterms → 𝕃 term
erase-lterms-if tt = erase-lterms
erase-lterms-if ff t lt = lterms-to-𝕃' t lt

{-
num-to-ℕ : num → ℕ
num-to-ℕ n with string-to-ℕ n
num-to-ℕ _ | just n = n
num-to-ℕ _ | _ = 0
-}

imps-to-cmds : imports → cmds
imps-to-cmds ImportsStart = CmdsStart
imps-to-cmds (ImportsNext i is) = CmdsNext (ImportCmd i) (imps-to-cmds is)

-- TODO handle qualif & module args
get-imports : start → 𝕃 string
get-imports (File _ is _ _ mn _ cs _) = imports-to-include is ++ get-imports-cmds cs
  where import-to-include : imprt → string
        import-to-include (Import _ _ _ x oa _ _) = x
        imports-to-include : imports → 𝕃 string
        imports-to-include ImportsStart = []
        imports-to-include (ImportsNext x is) = import-to-include x :: imports-to-include is
        singleton-if-include : cmd → 𝕃 string
        singleton-if-include (ImportCmd imp) = [ import-to-include imp ]
        singleton-if-include _ = []
        get-imports-cmds : cmds → 𝕃 string
        get-imports-cmds (CmdsNext c cs) = singleton-if-include c ++ get-imports-cmds cs
        get-imports-cmds CmdsStart = []

data language-level : Set where
  ll-term : language-level
  ll-type : language-level
  ll-kind : language-level

ll-to-string : language-level → string
ll-to-string ll-term = "term"
ll-to-string ll-type = "type"
ll-to-string ll-kind = "kind"

is-rho-plus : optPlus → 𝔹
is-rho-plus RhoPlus = tt
is-rho-plus _ = ff

is-equation : {ed : exprd} → ⟦ ed ⟧ → 𝔹
is-equation{TYPE} (TpParens _ t _) = is-equation t
is-equation{TYPE} (TpEq _ _ _ _) = tt
is-equation _ = ff 

is-equational : type → 𝔹
is-equational-kind : kind → 𝔹
is-equational-tk : tk → 𝔹
is-equational (Abs _ _ _ _ atk t2) = is-equational-tk atk || is-equational t2
is-equational (Iota _ _ _ t1 t2) = is-equational t1 || is-equational t2
is-equational (NoSpans t _) = is-equational t
is-equational (TpApp t1 t2) = is-equational t1 || is-equational t2
is-equational (TpAppt t1 _) = is-equational t1
is-equational (TpArrow t1 _ t2) = is-equational t1 || is-equational t2
is-equational (TpEq _ _ _ _) = tt
is-equational (TpLambda _ _ _ atk t2) = is-equational-tk atk || is-equational t2
is-equational (TpParens _ t _) = is-equational t
is-equational (Lft _ _ _ _ _) = ff
is-equational (TpVar _ t) = ff
is-equational (TpHole _) = ff --ACG
is-equational-tk (Tkt t1) = is-equational t1
is-equational-tk (Tkk k) = is-equational-kind k
is-equational-kind (KndArrow k1 k2) = is-equational-kind k1 || is-equational-kind k2
is-equational-kind (KndParens _ k _) = is-equational-kind k
is-equational-kind (KndPi _ _ _ atk k) = is-equational-tk atk || is-equational-kind k
is-equational-kind (KndTpArrow t1 k2) = is-equational t1 || is-equational-kind k2
is-equational-kind (KndVar _ _ _) = ff
is-equational-kind (Star _) = ff

split-var-h : 𝕃 char → 𝕃 char × 𝕃 char
split-var-h [] = [] , []
split-var-h ('.' :: xs) = [] , xs
split-var-h (x :: xs) with split-var-h xs
... | xs' , ys = (x :: xs') , ys

split-var : var → var × var
split-var v with split-var-h (reverse (string-to-𝕃char v))
... | xs , ys = 𝕃char-to-string (reverse ys) , 𝕃char-to-string (reverse xs)

var-suffix : var → maybe var
var-suffix v with split-var v
... | "" , _ = nothing
... | _ , sfx = just sfx

-- unique qualif domain prefixes
qual-pfxs : qualif → 𝕃 var
qual-pfxs q = uniq (prefixes (trie-strings q))
  where
  uniq : 𝕃 var → 𝕃 var
  uniq vs = stringset-strings (stringset-insert* empty-stringset vs)
  prefixes : 𝕃 var → 𝕃 var
  prefixes [] = []
  prefixes (v :: vs) with split-var v
  ... | "" , sfx = vs
  ... | pfx , sfx = pfx :: prefixes vs

unqual-prefix : qualif → 𝕃 var → var → var → var
unqual-prefix q [] sfx v = v
unqual-prefix q (pfx :: pfxs) sfx v
  with trie-lookup q (pfx # sfx)
... | just (v' , _) = if v =string v' then pfx # sfx else v
... | nothing = v

unqual-bare : qualif → var → var → var
unqual-bare q sfx v with trie-lookup q sfx
... | just (v' , _) = if v =string v' then sfx else v
... | nothing = v

unqual-local : var → var
unqual-local v = f (string-to-𝕃char v) [] where
  f : 𝕃 char → 𝕃 char → string
  f [] acc = 𝕃char-to-string (reverse acc)
  f ('@' :: t) acc = f t []
  f (h :: t) acc = f t (h :: acc)

unqual-all : qualif → var → string
unqual-all q v with var-suffix v
... | nothing = v
... | just sfx = unqual-bare q sfx (unqual-prefix q (qual-pfxs q) sfx v)

lam-expand-term : params → term → term
lam-expand-term (ParamsCons (Decl pi pi' x tk@(Tkt _) _) ps) t =
  Lam posinfo-gen KeptLambda pi' x NoClass (lam-expand-term ps t)
lam-expand-term (ParamsCons (Decl pi pi' x tk@(Tkk _) _) ps) t =
  lam-expand-term ps t
lam-expand-term ParamsNil t = t

lam-expand-type : params → type → type
lam-expand-type (ParamsCons (Decl pi pi' x tk _) ps) t =
  TpLambda posinfo-gen pi' x tk (lam-expand-type ps t)
lam-expand-type ParamsNil t = t

abs-expand-type : params → type → type
abs-expand-type (ParamsCons (Decl pi pi' x tk _) ps) t =
  Abs posinfo-gen Pi pi' x tk (abs-expand-type ps t)
abs-expand-type ParamsNil t = t

abs-expand-kind : params → kind → kind
abs-expand-kind (ParamsCons (Decl pi pi' x tk _) ps) k =
  KndPi posinfo-gen pi' x tk (abs-expand-kind ps k)
abs-expand-kind ParamsNil k = k

args-length : args → ℕ
args-length (ArgsCons p ps) = suc (args-length ps)
args-length ArgsNil = 0

erased-args-length : args → ℕ
erased-args-length (ArgsCons (TermArg _) ps) = suc (erased-args-length ps)
erased-args-length (ArgsCons (TypeArg _) ps) = erased-args-length ps
erased-args-length ArgsNil = 0

me-args-length : maybeErased → args → ℕ
me-args-length Erased = erased-args-length
me-args-length NotErased = args-length

spine : Set
spine = 𝕃(maybeErased × arg)

spineApp : Set
spineApp = (posinfo × qvar) × spine

term-to-spapp : term → maybe spineApp
term-to-spapp (App t me t') = term-to-spapp t ≫=maybe
  (λ { (v , as) → just (v , (me , TermArg t') :: as) })
term-to-spapp (AppTp t T) = term-to-spapp t ≫=maybe
  (λ { (v , as) → just (v , (NotErased , TypeArg T) :: as) })
term-to-spapp (Var pi v) = just ((pi , v) , [])
term-to-spapp _ = nothing

type-to-spapp : type → maybe spineApp
type-to-spapp (TpApp T T') = type-to-spapp T ≫=maybe
  (λ { (v , as) → just (v , (NotErased , TypeArg T') :: as) })
type-to-spapp (TpAppt T t) = type-to-spapp T ≫=maybe
  (λ { (v , as) → just (v , (NotErased , TermArg t) :: as) })
type-to-spapp (TpVar pi v) = just ((pi , v) , [])
type-to-spapp _ = nothing

spapp-term : spineApp → term
spapp-term ((pi , v) , []) = Var pi v
spapp-term (v , (me , TermArg t) :: as) = App (spapp-term (v , as)) me t
spapp-term (v , (me , TypeArg T) :: as) = AppTp (spapp-term (v , as)) T

spapp-type : spineApp → type
spapp-type ((pi , v) , []) = TpVar pi v
spapp-type (v , (me , TermArg t) :: as) = TpAppt (spapp-type (v , as)) t
spapp-type (v , (me , TypeArg T) :: as) = TpApp (spapp-type (v , as)) T

num-gt : num → ℕ → 𝕃 string
num-gt n n' = maybe-else [] (λ n'' → if n'' > n' then [ n ] else []) (string-to-ℕ n)
nums-gt : nums → ℕ → 𝕃 string
nums-gt (NumsStart n) n' = num-gt n n'
nums-gt (NumsNext n ns) n' =
  maybe-else [] (λ n'' → if n'' > n' || iszero n'' then [ n ] else []) (string-to-ℕ n)
  ++ nums-gt ns n'

nums-to-stringset : nums → stringset × 𝕃 string {- Repeated numbers -}
nums-to-stringset (NumsStart n) = stringset-insert empty-stringset n , []
nums-to-stringset (NumsNext n ns) with nums-to-stringset ns
...| ss , rs = if stringset-contains ss n
  then ss , n :: rs
  else stringset-insert ss n , rs

optNums-to-stringset : optNums → maybe stringset × (ℕ → maybe string)
optNums-to-stringset NoNums = nothing , λ _ → nothing
optNums-to-stringset (SomeNums ns) with nums-to-stringset ns
...| ss , [] = just ss , λ n → case nums-gt ns n of λ where
  [] → nothing
  ns-g → just ("Occurrences not found: " ^ 𝕃-to-string id ", " ns-g ^ " (total occurrences: " ^ ℕ-to-string n ^ ")")
...| ss , rs = just ss , λ n →
  just ("The list of occurrences contains the following repeats: " ^ 𝕃-to-string id ", " rs)
