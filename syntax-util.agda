module syntax-util where

open import lib
open import cedille-types

posinfo-gen : posinfo
posinfo-gen = "generated"

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
term-start-pos (Lam pi x x₁ x₂ t) = pi
term-start-pos (Parens pi t pi') = pi
term-start-pos (Var pi x₁) = pi

type-start-pos (Abs pi _ _ _ _) = pi
type-start-pos (Lft pi _ _) = pi
type-start-pos (TpApp t t₁) = type-start-pos t
type-start-pos (TpAppt t x) = type-start-pos t
type-start-pos (TpArrow t t₁) = type-start-pos t
type-start-pos (TpEq x x₁) = term-start-pos x
type-start-pos (TpParens pi _ pi') = pi
type-start-pos (TpVar pi x₁) = pi

kind-start-pos (KndArrow k k₁) = kind-start-pos k
kind-start-pos (KndParens pi k pi') = pi
kind-start-pos (KndPi pi x x₁ k) = pi
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

term-end-pos (App t x t') = term-end-pos t'
term-end-pos (AppTp t tp) = type-end-pos tp
term-end-pos (Hole pi) = posinfo-plus pi 1
term-end-pos (Lam pi x x₁ x₂ t) = term-end-pos t
term-end-pos (Parens pi t pi') = pi'
term-end-pos (Var pi x) = posinfo-plus-str pi x

type-end-pos (Abs pi _ _ _ t) = type-end-pos t
type-end-pos (Lft pi _ t) = liftingType-end-pos t
type-end-pos (TpApp t t') = type-end-pos t'
type-end-pos (TpAppt t x) = term-end-pos x
type-end-pos (TpArrow t t') = type-end-pos t'
type-end-pos (TpEq x x') = term-end-pos x'
type-end-pos (TpParens pi _ pi') = pi'
type-end-pos (TpVar pi x) = posinfo-plus-str pi x

kind-end-pos (KndArrow k k') = kind-end-pos k'
kind-end-pos (KndParens pi k pi') = pi'
kind-end-pos (KndPi pi x x₁ k) = kind-end-pos k
kind-end-pos (KndTpArrow x k) = kind-end-pos k
kind-end-pos (KndVar pi x) = posinfo-plus-str pi x
kind-end-pos (Star pi) = pi

liftingType-end-pos (LiftArrow l l') = liftingType-end-pos l'
liftingType-end-pos (LiftParens pi l pi') = pi'
liftingType-end-pos (LiftPi x x₁ x₂ l) = liftingType-end-pos l
liftingType-end-pos (LiftStar pi) = posinfo-plus pi 1
liftingType-end-pos (LiftTpArrow x l) = liftingType-end-pos l

decls-start-pos : decls → posinfo
decls-start-pos (DeclsCons (Decl pi _ _ _) _) = pi
decls-start-pos (DeclsNil pi) = pi

decls-end-pos : decls → posinfo
decls-end-pos (DeclsCons _ ds) = decls-end-pos ds
decls-end-pos (DeclsNil pi) = pi

ctordeclsne-end-pos : ctordeclsne → posinfo
ctordeclsne-end-pos (CtordeclsneNext _ c) = ctordeclsne-end-pos c
ctordeclsne-end-pos (CtordeclsneStart (Ctordecl _ _ _ pi)) = pi

ctordecls-end-pos : ctordecls → posinfo
ctordecls-end-pos (Ctordeclse pi) = pi
ctordecls-end-pos (Ctordeclsne x) = ctordeclsne-end-pos x

tk-arrow-kind : tk → kind → kind
tk-arrow-kind (Tkk k) k' = KndArrow k k'
tk-arrow-kind (Tkt t) k = KndTpArrow t k

TpApp-tk : type → var → tk → type
TpApp-tk tp x (Tkk _) = TpApp tp (TpVar posinfo-gen x)
TpApp-tk tp x (Tkt _) = TpAppt tp (Var posinfo-gen x)

