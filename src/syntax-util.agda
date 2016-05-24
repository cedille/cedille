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

indices-to-decls : indices → decls
indices-to-decls (Indicese pi) = (DeclsNil pi)
indices-to-decls (Indicesne x) = x

term-start-pos : term → posinfo
type-start-pos : type → posinfo
kind-start-pos : kind → posinfo
liftingType-start-pos : liftingType → posinfo

term-start-pos (App t x t₁) = term-start-pos t
term-start-pos (AppTp t tp) = term-start-pos t
term-start-pos (Hole pi) = pi
term-start-pos (Lam pi x _ x₁ x₂ t) = pi
term-start-pos (Parens pi t pi') = pi
term-start-pos (Var pi x₁) = pi
term-start-pos (Beta pi) = pi
term-start-pos (Delta pi _) = pi
term-start-pos (PiInj pi _ _) = pi
term-start-pos (Epsilon pi _ _ _) = pi
term-start-pos (Rho pi _ _) = pi
term-start-pos (Chi pi _ _) = pi
term-start-pos (Sigma pi _) = pi
term-start-pos (Theta pi _ _ _) = pi

type-start-pos (Abs pi _ _ _ _ _) = pi
type-start-pos (TpLambda pi _ _ _ _) = pi
type-start-pos (Iota pi _ _ _) = pi
type-start-pos (Lft pi _ _ _ _) = pi
type-start-pos (TpApp t t₁) = type-start-pos t
type-start-pos (TpAppt t x) = type-start-pos t
type-start-pos (TpArrow t t₁) = type-start-pos t
type-start-pos (TpEq x x₁) = term-start-pos x
type-start-pos (TpParens pi _ pi') = pi
type-start-pos (TpVar pi x₁) = pi
type-start-pos (NoSpans t _) = type-start-pos t -- we are not expecting this on input

kind-start-pos (KndArrow k k₁) = kind-start-pos k
kind-start-pos (KndParens pi k pi') = pi
kind-start-pos (KndPi pi _ x x₁ k) = pi
kind-start-pos (KndTpArrow x k) = type-start-pos x
kind-start-pos (KndVar pi x₁) = pi
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

term-end-pos (App t x t') = term-end-pos t'
term-end-pos (AppTp t tp) = type-end-pos tp
term-end-pos (Hole pi) = posinfo-plus pi 1
term-end-pos (Lam pi x _ x₁ x₂ t) = term-end-pos t
term-end-pos (Parens pi t pi') = pi'
term-end-pos (Var pi x) = posinfo-plus-str pi x
term-end-pos (Beta pi) = posinfo-plus pi 1
term-end-pos (Delta pi t) = term-end-pos t
term-end-pos (PiInj _ _ t) = term-end-pos t
term-end-pos (Epsilon pi _ _ t) = term-end-pos t
term-end-pos (Rho pi t t') = term-end-pos t'
term-end-pos (Chi pi T t') = term-end-pos t'
term-end-pos (Sigma pi t) = term-end-pos t
term-end-pos (Theta _ _ _ ls) = lterms-end-pos ls

type-end-pos (Abs pi _ _ _ _ t) = type-end-pos t
type-end-pos (TpLambda _ _ _ _ t) = type-end-pos t
type-end-pos (Iota _ _ _ tp) = type-end-pos tp
type-end-pos (Lft pi _ _ _ t) = liftingType-end-pos t
type-end-pos (TpApp t t') = type-end-pos t'
type-end-pos (TpAppt t x) = term-end-pos x
type-end-pos (TpArrow t t') = type-end-pos t'
type-end-pos (TpEq x x') = term-end-pos x'
type-end-pos (TpParens pi _ pi') = pi'
type-end-pos (TpVar pi x) = posinfo-plus-str pi x
type-end-pos (NoSpans t pi) = pi

kind-end-pos (KndArrow k k') = kind-end-pos k'
kind-end-pos (KndParens pi k pi') = pi'
kind-end-pos (KndPi pi _ x x₁ k) = kind-end-pos k
kind-end-pos (KndTpArrow x k) = kind-end-pos k
kind-end-pos (KndVar pi x) = posinfo-plus-str pi x
kind-end-pos (Star pi) = posinfo-plus pi 1

liftingType-end-pos (LiftArrow l l') = liftingType-end-pos l'
liftingType-end-pos (LiftParens pi l pi') = pi'
liftingType-end-pos (LiftPi x x₁ x₂ l) = liftingType-end-pos l
liftingType-end-pos (LiftStar pi) = posinfo-plus pi 1
liftingType-end-pos (LiftTpArrow x l) = liftingType-end-pos l

lterms-end-pos (LtermsNil pi) = posinfo-plus pi 1 -- must add one for the implicit Beta that we will add at the end
lterms-end-pos (LtermsCons _ ls) = lterms-end-pos ls

decls-start-pos : decls → posinfo
decls-start-pos (DeclsCons (Decl pi _ _ _) _) = pi
decls-start-pos (DeclsNil pi) = pi

decls-end-pos : decls → posinfo
decls-end-pos (DeclsCons _ ds) = decls-end-pos ds
decls-end-pos (DeclsNil pi) = pi

ctordeclsne-end-pos : ctordeclsne → posinfo
ctordeclsne-end-pos (CtordeclsneNext _ c) = ctordeclsne-end-pos c
ctordeclsne-end-pos (CtordeclsneStart (Ctordecl _ _ tp)) = type-end-pos tp

ctordecls-end-pos : ctordecls → posinfo
ctordecls-end-pos (Ctordeclse pi) = pi
ctordecls-end-pos (Ctordeclsne x) = ctordeclsne-end-pos x

udefsne-start-pos : udefsne → posinfo
udefsne-start-pos (UdefsneNext (Udef pi x t) us) = pi
udefsne-start-pos (UdefsneStart (Udef pi x t)) = pi

udefs-start-pos : udefs → posinfo
udefs-start-pos (Udefse pi) = pi
udefs-start-pos (Udefsne x) = udefsne-start-pos x

udefsne-end-pos : udefsne → posinfo
udefsne-end-pos (UdefsneNext _ us) = udefsne-end-pos us
udefsne-end-pos (UdefsneStart (Udef pi x t)) = term-end-pos t

udefs-end-pos : udefs → posinfo
udefs-end-pos (Udefse pi) = posinfo-plus pi 1
udefs-end-pos (Udefsne x) = udefsne-end-pos x

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

is-app : {ed : exprd} → ⟦ ed ⟧ → 𝔹
is-app{TERM} (App _ _ _) = tt
is-app{TERM} (AppTp _ _) = tt
is-app{TYPE} (TpApp _ _) = tt
is-app{TYPE} (TpAppt _ _) = tt
is-app _ = ff

is-arrow : {ed : exprd} → ⟦ ed ⟧ → 𝔹
is-arrow{TYPE} (TpArrow _ _) = tt
is-arrow{KIND} (KndTpArrow _ _) = tt
is-arrow{KIND} (KndArrow _ _) = tt
is-arrow{LIFTINGTYPE} (LiftArrow _ _) = tt
is-arrow{LIFTINGTYPE} (LiftTpArrow _ _) = tt
is-arrow _ = ff

is-abs : {ed : exprd} → ⟦ ed ⟧ → 𝔹
is-abs{TERM} (Lam _ _ _ _ _ _) = tt
is-abs{TYPE} (Abs _ _ _ _ _ _) = tt
is-abs{TYPE} (TpLambda _ _ _ _ _) = tt
is-abs{TYPE} (Iota _ _ _ _) = tt
is-abs{KIND} (KndPi _ _ _ _ _) = tt
is-abs{LIFTINGTYPE} (LiftPi _ _ _ _) = tt
is-abs _ = ff


eq-maybeErased : maybeErased → maybeErased → 𝔹
eq-maybeErased Erased Erased = tt
eq-maybeErased Erased NotErased = ff
eq-maybeErased NotErased Erased = ff
eq-maybeErased NotErased NotErased = tt

forall-bind-decls : decls → type → type
forall-bind-decls (DeclsCons (Decl _ x atk _) ds) tp = Abs posinfo-gen All posinfo-gen x atk (forall-bind-decls ds tp)
forall-bind-decls (DeclsNil x) tp = tp

tplam-bind-decls : decls → type → type
tplam-bind-decls (DeclsCons (Decl _ x atk _) ds) tp = TpLambda posinfo-gen posinfo-gen x atk (tplam-bind-decls ds tp)
tplam-bind-decls (DeclsNil x) tp = tp

erased-lambda-bind-decls : decls → term → term
erased-lambda-bind-decls (DeclsCons (Decl _ x atk _) ds) tp = 
  Lam posinfo-gen ErasedLambda posinfo-gen x (SomeClass atk) (erased-lambda-bind-decls ds tp)
erased-lambda-bind-decls (DeclsNil x) tp = tp

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

App* : term → 𝕃 term → term
App* t [] = t
App* t (arg :: args) = App (App* t args) NotErased arg

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
is-intro-form (Lam x x₁ x₂ x₃ x₄ t) = tt
is-intro-form _ = ff

erase-term : term → term
erase-lterms : theta → lterms → 𝕃 term
erase-term (Parens _ t _) = erase-term t
erase-term (App t1 Erased t2) = erase-term t1
erase-term (App t1 NotErased t2) = App (erase-term t1) NotErased (erase-term t2)
erase-term (AppTp t tp) = erase-term t
erase-term (Lam _ ErasedLambda _ _ _ t) = erase-term t
erase-term (Lam pi KeptLambda pi' x oc t) = Lam pi KeptLambda pi' x NoClass (erase-term t)
erase-term (Var pi x) = Var pi x
erase-term (Beta pi) = Beta pi
erase-term (Delta pi t) = Var posinfo-gen "[erased-proof]"
erase-term (PiInj _ _ t) = erase-term t
erase-term (Epsilon pi lr _ t) = erase-term t
erase-term (Sigma pi t) = erase-term t
erase-term (Hole pi) = Hole pi
erase-term (Rho pi t t') = erase-term t'
erase-term (Chi pi T t') = erase-term t'
erase-term (Theta pi u t ls) = App*' (erase-term t) (erase-lterms u ls)

erase-lterms Abstract (LtermsNil _) = []
erase-lterms (AbstractVars _) (LtermsNil _) = []
erase-lterms AbstractEq (LtermsNil pi) = [ Beta pi ]
erase-lterms u (LtermsCons t ls) = erase-term t :: erase-lterms u ls

lterms-to-𝕃h : theta → lterms → 𝕃 term
lterms-to-𝕃h Abstract (LtermsNil _) = []
lterms-to-𝕃h (AbstractVars _) (LtermsNil _) = []
lterms-to-𝕃h AbstractEq (LtermsNil pi) = [ Beta pi ]
lterms-to-𝕃h u (LtermsCons t ls) = t :: (lterms-to-𝕃h u ls)

lterms-to-𝕃 : theta → lterms → 𝕃 term
lterms-to-𝕃 u ls = reverse (lterms-to-𝕃h u ls)

num-to-ℕ : num → ℕ
num-to-ℕ n with string-to-ℕ n
num-to-ℕ _ | just n = n
num-to-ℕ _ | _ = 0

compute-deps : start → 𝕃 string
compute-deps (File _ cs _) = compute-deps-cmds cs
  where singleton-if-include : cmd → 𝕃 string
        singleton-if-include (Import _ x _) = [ x ]
        singleton-if-include _ = []
        compute-deps-cmds : cmds → 𝕃 string
        compute-deps-cmds (CmdsNext c cs) = singleton-if-include c ++ compute-deps-cmds cs
        compute-deps-cmds (CmdsStart c) = singleton-if-include c
