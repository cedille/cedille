module syntax-util where

open import lib
open import cedille-types

posinfo-gen : posinfo
posinfo-gen = "generated"

first-position : posinfo
first-position = "1"

dummy-var : var
dummy-var = "_dummy"

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
term-start-pos (Unfold pi _) = pi
term-start-pos (Parens pi t pi') = pi
term-start-pos (Var pi x₁) = pi
term-start-pos (Beta pi _) = pi
term-start-pos (Delta pi _) = pi
term-start-pos (Omega pi _) = pi
term-start-pos (InlineDef pi _ _ _ _) = pi
term-start-pos (IotaPair pi _ _ _ _) = pi
term-start-pos (IotaProj t _ _) = term-start-pos t
term-start-pos (PiInj pi _ _) = pi
term-start-pos (Epsilon pi _ _ _) = pi
term-start-pos (Rho pi _ _ _) = pi
term-start-pos (Chi pi _ _) = pi
term-start-pos (Sigma pi _) = pi
term-start-pos (Theta pi _ _ _) = pi

type-start-pos (Abs pi _ _ _ _ _) = pi
type-start-pos (Mu pi _ _ _ _) = pi
type-start-pos (TpLambda pi _ _ _ _) = pi
type-start-pos (IotaEx pi _ _ _ _ _) = pi
type-start-pos (Lft pi _ _ _ _) = pi
type-start-pos (TpApp t t₁) = type-start-pos t
type-start-pos (TpAppt t x) = type-start-pos t
type-start-pos (TpArrow t _ t₁) = type-start-pos t
type-start-pos (TpEq x x₁) = term-start-pos x
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
lterms-end-pos : lterms → posinfo
args-end-pos : args → posinfo

term-end-pos (App t x t') = term-end-pos t'
term-end-pos (AppTp t tp) = type-end-pos tp
term-end-pos (Hole pi) = posinfo-plus pi 1
term-end-pos (Lam pi x _ x₁ x₂ t) = term-end-pos t
term-end-pos (Unfold _ t) = term-end-pos t
term-end-pos (Parens pi t pi') = pi'
term-end-pos (Var pi x) = posinfo-plus-str pi x
term-end-pos (Beta pi NoTerm) = posinfo-plus pi 1
term-end-pos (Beta pi (SomeTerm t pi')) = pi'
term-end-pos (Omega pi t) = term-end-pos t
term-end-pos (Delta pi t) = term-end-pos t
term-end-pos (InlineDef _ _ _ _ pi) = pi
term-end-pos (IotaPair _ _ _ _ pi) = pi
term-end-pos (IotaProj _ _ pi) = pi
term-end-pos (PiInj _ _ t) = term-end-pos t
term-end-pos (Epsilon pi _ _ t) = term-end-pos t
term-end-pos (Rho pi _ t t') = term-end-pos t'
term-end-pos (Chi pi T t') = term-end-pos t'
term-end-pos (Sigma pi t) = term-end-pos t
term-end-pos (Theta _ _ _ ls) = lterms-end-pos ls

type-end-pos (Abs pi _ _ _ _ t) = type-end-pos t
type-end-pos (Mu pi _ _ _ t) = type-end-pos t
type-end-pos (TpLambda _ _ _ _ t) = type-end-pos t
type-end-pos (IotaEx _ _ _ _ _ tp) = type-end-pos tp
type-end-pos (Lft pi _ _ _ t) = liftingType-end-pos t
type-end-pos (TpApp t t') = type-end-pos t'
type-end-pos (TpAppt t x) = term-end-pos x
type-end-pos (TpArrow t _ t') = type-end-pos t'
type-end-pos (TpEq x x') = term-end-pos x'
type-end-pos (TpParens pi _ pi') = pi'
type-end-pos (TpVar pi x) = posinfo-plus-str pi x
type-end-pos (TpHole pi) = pi --ACG
type-end-pos (NoSpans t pi) = pi

kind-end-pos (KndArrow k k') = kind-end-pos k'
kind-end-pos (KndParens pi k pi') = pi'
kind-end-pos (KndPi pi _ x x₁ k) = kind-end-pos k
kind-end-pos (KndTpArrow x k) = kind-end-pos k
kind-end-pos (KndVar pi x ys) = args-end-pos ys
kind-end-pos (Star pi) = posinfo-plus pi 1

args-end-pos (ArgsCons x ys) = args-end-pos ys
args-end-pos (ArgsNil pi) = pi

liftingType-end-pos (LiftArrow l l') = liftingType-end-pos l'
liftingType-end-pos (LiftParens pi l pi') = pi'
liftingType-end-pos (LiftPi x x₁ x₂ l) = liftingType-end-pos l
liftingType-end-pos (LiftStar pi) = posinfo-plus pi 1
liftingType-end-pos (LiftTpArrow x l) = liftingType-end-pos l

lterms-end-pos (LtermsNil pi) = posinfo-plus pi 1 -- must add one for the implicit Beta that we will add at the end
lterms-end-pos (LtermsCons _ _ ls) = lterms-end-pos ls

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

⟦_⟧ : exprd → Set
⟦ TERM ⟧ = term
⟦ TYPE ⟧ = type
⟦ KIND ⟧ = kind
⟦ LIFTINGTYPE ⟧ = liftingType

exprd-name : exprd → string
exprd-name TERM = "term"
exprd-name TYPE = "type"
exprd-name KIND = "kind"
exprd-name LIFTINGTYPE = "lifting type"

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
is-abs{TERM} (Lam _ _ _ _ _ _) = tt
is-abs{TYPE} (Abs _ _ _ _ _ _) = tt
is-abs{TYPE} (TpLambda _ _ _ _ _) = tt
is-abs{TYPE} (IotaEx _ _ _ _ _ _) = tt
is-abs{KIND} (KndPi _ _ _ _ _) = tt
is-abs{LIFTINGTYPE} (LiftPi _ _ _ _) = tt
is-abs _ = ff

is-beta : {ed : exprd} → ⟦ ed ⟧ → 𝔹
is-beta{TERM} (Beta _ _) = tt
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
eq-binder _ _ = tt

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

erase-term : term → term
erase-lterms : theta → lterms → 𝕃 term
erase-term (Parens _ t _) = erase-term t
erase-term (App t1 Erased t2) = erase-term t1
erase-term (App t1 NotErased t2) = App (erase-term t1) NotErased (erase-term t2)
erase-term (AppTp t tp) = erase-term t
erase-term (Lam _ ErasedLambda _ _ _ t) = erase-term t
erase-term (Lam pi KeptLambda pi' x oc t) = Lam pi KeptLambda pi' x NoClass (erase-term t)
erase-term (Unfold _ t) = erase-term t
erase-term (Var pi x) = Var pi x
erase-term (Beta pi NoTerm) = Beta pi NoTerm
erase-term (Beta pi (SomeTerm t _)) = erase-term t
erase-term (Delta pi t) = Beta pi NoTerm -- we need to erase the body t, so just use Beta as the name for any erased proof
erase-term (Omega pi t) = erase-term t
erase-term (InlineDef pi pi' x t pi'') = InlineDef pi pi' x (erase-term t) pi''
erase-term (IotaPair pi t1 t2 ot pi') = erase-term t1
erase-term (IotaProj t n pi) = erase-term t
erase-term (PiInj _ _ t) = erase-term t
erase-term (Epsilon pi lr _ t) = erase-term t
erase-term (Sigma pi t) = erase-term t
erase-term (Hole pi) = Hole pi
erase-term (Rho pi _ t t') = erase-term t'
erase-term (Chi pi T t') = erase-term t'
erase-term (Theta pi u t ls) = App*' (erase-term t) (erase-lterms u ls)

erase-lterms Abstract (LtermsNil _) = []
erase-lterms (AbstractVars _) (LtermsNil _) = []
erase-lterms AbstractEq (LtermsNil pi) = [ Beta pi NoTerm ]
erase-lterms u (LtermsCons NotErased t ls) = (erase-term t) :: erase-lterms u ls
erase-lterms u (LtermsCons Erased t ls) = erase-lterms u ls

lterms-to-𝕃h : theta → lterms → 𝕃 (maybeErased × term)
lterms-to-𝕃h Abstract (LtermsNil _) = []
lterms-to-𝕃h (AbstractVars _) (LtermsNil _) = []
lterms-to-𝕃h AbstractEq (LtermsNil pi) = [ NotErased , Beta pi NoTerm ]
lterms-to-𝕃h u (LtermsCons m t ls) = (m , t) :: (lterms-to-𝕃h u ls)

lterms-to-𝕃 : theta → lterms → 𝕃 (maybeErased × term)
lterms-to-𝕃 u ls = reverse (lterms-to-𝕃h u ls)

num-to-ℕ : num → ℕ
num-to-ℕ n with string-to-ℕ n
num-to-ℕ _ | just n = n
num-to-ℕ _ | _ = 0

get-imports : start → 𝕃 string
get-imports (File _ cs _) = get-imports-cmds cs
  where singleton-if-include : cmd → 𝕃 string
        singleton-if-include (Import _ x _) = [ x ]
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

is-rho-plus : rho → 𝔹
is-rho-plus RhoPlain = ff
is-rho-plus RhoPlus = tt

is-equation : type → 𝔹
is-equation (TpParens _ t _) = is-equation t
is-equation (TpEq _ _) = tt
is-equation _ = ff 

is-equational : type → 𝔹
is-equational-kind : kind → 𝔹
is-equational-tk : tk → 𝔹
is-equational (Abs _ _ _ _ atk t2) = is-equational-tk atk || is-equational t2
is-equational (Mu _ _ _ k t) = is-equational-kind k || is-equational t
is-equational (IotaEx _ _ _ _ (SomeType t1) t2) = is-equational t1 || is-equational t2
is-equational (IotaEx _ _ _ _ _ t2) = is-equational t2
is-equational (NoSpans t _) = is-equational t
is-equational (TpApp t1 t2) = is-equational t1 || is-equational t2
is-equational (TpAppt t1 _) = is-equational t1
is-equational (TpArrow t1 _ t2) = is-equational t1 || is-equational t2
is-equational (TpEq _ _) = tt
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

ie-eq : ie → ie → 𝔹
ie-eq Exists Exists = tt
ie-eq Exists Iota = ff
ie-eq Iota Exists = ff
ie-eq Iota Iota = tt
