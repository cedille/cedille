module cedille-syntax where
--open import lib
open import string
open import bool
open import unit
open import syntax-util
open import general-util
open import cedille-types
open import erase

tm-tp-lift : 𝔹 → Set
tm-tp-lift tt = term
tm-tp-lift ff = type

tp-kd-lift : 𝔹 → Set
tp-kd-lift tt = type
tp-kd-lift ff = kind

language-level-lift : language-level → Set
language-level-lift ll-term = term
language-level-lift ll-type = type
language-level-lift ll-kind = kind

|`_`| = erase

$⊤ : ∀ {ℓ} {X : Set ℓ} → (⊤ → X) → X
$⊤ f = f triv

-- App, AppTp, TpApp, TpAppt
infixl 10 _`_ _-_ _·_

_-_ = flip App Erased

_`_ : ∀ {ll : 𝔹} → tm-tp-lift ll → term → tm-tp-lift ll
_`_ {tt} = mapp
_`_ {ff} = TpAppt

_·_ : ∀ {ll : 𝔹} → tm-tp-lift ll → type → tm-tp-lift ll
_·_ {tt} = AppTp
_·_ {ff} = TpApp

-- Beta
infix 9 β<_> β[_] β<_>[_]
β = Beta pi-gen NoTerm NoTerm
β<_> = λ t → Beta pi-gen (SomeTerm t pi-gen) NoTerm
β[_] = λ t → Beta pi-gen NoTerm (SomeTerm t pi-gen)
β<_>[_] = λ t t' → Beta pi-gen (SomeTerm t pi-gen) (SomeTerm t' pi-gen)

-- Chi
infixr 8 χ-_ χ_-_
χ-_ = Chi pi-gen NoType
χ_-_ = λ T t → Chi pi-gen (SomeType T) t

-- Delta
infixr 8 δ-_ δ_-_
δ-_ = Delta pi-gen NoType
δ_-_ = λ T t → Delta pi-gen (SomeType T) t

-- Epsilon
infixr 8 ε_ εl_ εr_ ε-_ εl-_ εr-_
ε_ = Epsilon pi-gen Both ff
εl_ = Epsilon pi-gen Left ff
εr_ = Epsilon pi-gen Right ff
ε-_ = Epsilon pi-gen Both tt
εl-_ = Epsilon pi-gen Left tt
εr-_ = Epsilon pi-gen Right tt

-- Hole
● : ∀ {ll : 𝔹} → tm-tp-lift ll
● {tt} = Hole pi-gen
● {ff} = TpHole pi-gen
--● = Hole pi-gen

-- IotaPair ("₊" = "\_+")
[_`,_] = λ t₁ t₂ → IotaPair pi-gen t₁ t₂ NoGuide pi-gen
[_`,_*_₊_] = λ t₁ t₂ x T → IotaPair pi-gen t₁ t₂ (Guide pi-gen x T) pi-gen

-- IotaProj
infixl 5 _₊1 _₊2 _₊#_
_₊1 = λ t → IotaProj t "1" pi-gen
_₊2 = λ t → IotaProj t "2" pi-gen
_₊#_ = λ t n → IotaProj t n pi-gen

-- Lam, TpLambda
infixr 4 λ`_₊_ λ`_:`_₊_ Λ_₊_ Λ_:`_₊_
λ`_:`_₊_ : ∀ {ll ll' : 𝔹} → var → tp-kd-lift ll → tm-tp-lift ll' → tm-tp-lift ll'
Λ_:`_₊_ : ∀ {ll : 𝔹} → var → tp-kd-lift ll → term → term

λ`_₊_ = flip (Lam pi-gen NotErased pi-gen) NoClass
Λ_₊_ = flip (Lam pi-gen Erased pi-gen) NoClass
λ`_:`_₊_ {tt}{ff} x = TpLambda pi-gen pi-gen x ∘ Tkt
λ`_:`_₊_ {ff}{ff} x = TpLambda pi-gen pi-gen x ∘ Tkk
λ`_:`_₊_ {tt}{tt} x = Lam pi-gen NotErased pi-gen x ∘' SomeClass ∘' Tkt
λ`_:`_₊_ {ff}{tt} x = Lam pi-gen NotErased pi-gen x ∘' SomeClass ∘' Tkk
Λ_:`_₊_ {tt} x = Lam pi-gen Erased pi-gen x ∘' SomeClass ∘' Tkt
Λ_:`_₊_ {ff} x = Lam pi-gen Erased pi-gen x ∘' SomeClass ∘' Tkk

-- Let
infixr 8 [_=`_]-_ [_:`_=`_]-_ -[_=`_]-_ -[_:`_=`_]-_
[_:`_=`_]-_ : ∀ {ll ll' : 𝔹} → var → tp-kd-lift ll → tm-tp-lift ll → tm-tp-lift ll' → tm-tp-lift ll'
-[_:`_=`_]-_ : ∀ {ll : 𝔹} → var → tp-kd-lift ll → tm-tp-lift ll → term → term

[_=`_]-_ = λ x t t' → Let pi-gen NotErased (DefTerm pi-gen x NoType t) t'
-[_=`_]-_ = λ x t t' → Let pi-gen Erased (DefTerm pi-gen x NoType t) t'
[_:`_=`_]-_ {tt}{tt} x T = Let pi-gen NotErased ∘ DefTerm pi-gen x (SomeType T)
[_:`_=`_]-_ {tt}{ff} x T = TpLet pi-gen ∘ DefTerm pi-gen x (SomeType T)
[_:`_=`_]-_ {ff}{tt} x k = Let pi-gen NotErased ∘ DefType pi-gen x k
[_:`_=`_]-_ {ff}{ff} x k = TpLet pi-gen ∘ DefType pi-gen x k
-[_:`_=`_]-_ {tt} x T = Let pi-gen Erased ∘ DefTerm pi-gen x (SomeType T)
-[_:`_=`_]-_ {ff} x k = Let pi-gen Erased ∘ DefType pi-gen x k



-- Open
infixr 8 open`_-_ close_-_
open`_-_ = Open pi-gen OpacTrans pi-gen
close_-_ = Open pi-gen OpacOpaque pi-gen

--Parens
⦅_⦆ : ∀ {ll : language-level} → language-level-lift ll → language-level-lift ll
⦅_⦆{ll-term} = flip (Parens pi-gen) pi-gen
⦅_⦆{ll-type} = flip (TpParens pi-gen) pi-gen
⦅_⦆{ll-kind} = flip (KndParens pi-gen) pi-gen


-- Phi
infix 8 φ_-_[_]
φ_-_[_] = λ eq t₁ t₂ → Phi pi-gen eq t₁ t₂ pi-gen

-- Rho
infixr 8 ρ_-_ ρ<_>_-_ ρ_*_₊_-_ ρ<_>_*_₊_-_ ρ+_-_ ρ+<_>_-_ ρ+_*_₊_-_ ρ+<_>_*_₊_-_
ρ_-_ = λ t t' → Rho pi-gen ff NoNums t NoGuide t'
ρ<_>_-_ = λ ns t t' → Rho pi-gen ff (SomeNums ns) t NoGuide t'
ρ_*_₊_-_ = λ t x T t' → Rho pi-gen ff NoNums t (Guide pi-gen x T) t'
ρ<_>_*_₊_-_ = λ ns t x T t' → Rho pi-gen ff (SomeNums ns) t (Guide pi-gen x T) t'
ρ+_-_ = λ t t' → Rho pi-gen tt NoNums t NoGuide t'
ρ+<_>_-_ = λ ns t t' → Rho pi-gen tt (SomeNums ns) t NoGuide t'
ρ+_*_₊_-_ = λ t x T t' → Rho pi-gen tt NoNums t (Guide pi-gen x T) t'
ρ+<_>_*_₊_-_ = λ ns t x T t' → Rho pi-gen tt (SomeNums ns) t (Guide pi-gen x T) t'

-- Sigma
infixr 9 ς_
ς_ = Sigma pi-gen

-- Theta
infix 9 θ_`_ θ+_`_ θ<_>_`_
θ_`_ = λ t ts → Theta pi-gen Abstract t ts
θ+_`_ = λ t ts → Theta pi-gen AbstractEq t ts
θ<_>_`_ = λ vs t ts → Theta pi-gen (AbstractVars vs) t ts

-- Mu
infix 9 μ_₊_[_] μ_₊_*_[_]
μ_₊_[_] = λ x t ms → Mu pi-gen pi-gen x t NoType pi-gen ms pi-gen
μ_₊_*_[_] = λ x t T ms → Mu pi-gen pi-gen x t (SomeType T) pi-gen ms pi-gen

-- Mu'
infix 9 μ'_[_] μ'_*_[_] μ'<_>_[_] μ'<_>_*_[_]
μ'_[_] = λ t ms → Mu' pi-gen NoTerm t NoType pi-gen ms pi-gen
μ'_*_[_] = λ t T ms → Mu' pi-gen NoTerm t (SomeType T) pi-gen ms pi-gen
μ'<_>_[_] = λ t t' ms → Mu' pi-gen (SomeTerm t pi-gen) t' NoType pi-gen ms pi-gen
μ'<_>_*_[_] = λ t t' T ms → Mu' pi-gen (SomeTerm t pi-gen) t' (SomeType T) pi-gen ms pi-gen

-- Var, TpVar
infixr 11 ₓ_
ₓ_ : ∀ {ll : 𝔹} → var → tm-tp-lift ll

ₓ_ {tt} = Var pi-gen
ₓ_ {ff} = TpVar pi-gen



-- Abs, KndPi
infixr 5 ∀`_:`_₊_ Π_:`_₊_
∀`_:`_₊_ : ∀ {ll : 𝔹} → var → tp-kd-lift ll → type → type
Π_:`_₊_ : ∀ {ll ll' : 𝔹} → var → tp-kd-lift ll → tp-kd-lift ll' → tp-kd-lift ll'

∀`_:`_₊_ {tt} x = Abs pi-gen Erased pi-gen x ∘ Tkt
∀`_:`_₊_ {ff} x = Abs pi-gen Erased pi-gen x ∘ Tkk

Π_:`_₊_ {tt}{tt} x = Abs pi-gen NotErased pi-gen x ∘ Tkt
Π_:`_₊_ {ff}{tt} x = Abs pi-gen NotErased pi-gen x ∘ Tkk
Π_:`_₊_ {tt}{ff} x = KndPi pi-gen pi-gen x ∘ Tkt
Π_:`_₊_ {ff}{ff} x = KndPi pi-gen pi-gen x ∘ Tkk


-- Iota
infixr 4 ι_:`_₊_
ι_:`_₊_ = Iota pi-gen pi-gen

-- Lft
infix 4 ↑_₊_:ₗ_
↑_₊_:ₗ_ = Lft pi-gen pi-gen

-- NoSpans
infix 4 [^_^]
[^_^] = λ T → NoSpans T pi-gen

-- TpArrow, KndArrow, KndTpArrow
infixr 5 _➔_ _➾_  -- "➔" = "\r" (↕ 5, ↔ 1), "➾" = "\r" (↕ 7, ↔ 8)
_➔_ : ∀ {ll ll' : 𝔹} → tp-kd-lift ll → tp-kd-lift ll' → tp-kd-lift ll'

_➾_ = flip TpArrow Erased
_➔_ {tt}{tt} = flip TpArrow NotErased
_➔_ {ff}{tt} = const $ TpArrow (TpVar pi-gen "cedille-syntax.agda: error in _➔_ case") NotErased
_➔_ {tt}{ff} = KndTpArrow
_➔_ {ff}{ff} = KndArrow

-- TpEq
infix 4 [_≃_]
[_≃_] = λ t₁ t₂ → TpEq pi-gen t₁ t₂ pi-gen

-- KndVar
infix 11 κ_`_
κ_`_ = KndVar pi-gen

-- Star
★ = Star pi-gen
