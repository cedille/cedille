module cedille-syntax where
open import lib
open import ctxt
open import syntax-util
open import general-util
open import is-free
open import cedille-types

-- App, AppTp
infixl 10 _`_ _-_ _·_
-- Pattern and constructor
pattern _`_ t t' = App t NotErased t'
pattern _-_ t t' = App t Erased t'
pattern _·_ t T = AppTp t T

-- Beta
infix 9 β<_> β[_] β<_>[_] `β<_> `β[_] `β<_>[_]
pattern β = Beta _ NoTerm NoTerm
pattern β<_> t = Beta _ (SomeTerm t _) NoTerm
pattern β[_] t = Beta _ NoTerm (SomeTerm t _)
pattern β<_>[_] t t' = Beta _ (SomeTerm t _) (SomeTerm t' _)
`β = Beta pi-gen NoTerm NoTerm
`β<_> = λ t → Beta pi-gen (SomeTerm t pi-gen) NoTerm
`β[_] = λ t → Beta pi-gen NoTerm (SomeTerm t pi-gen)
`β<_>[_] = λ t t' → Beta pi-gen (SomeTerm t pi-gen) (SomeTerm t' pi-gen)

-- Chi
infixr 8 χ-_ χ_-_ `χ-_ `χ_-_
pattern χ-_ t = Chi _ NoType t
pattern χ_-_ T t = Chi _ (SomeType T) t
`χ-_ = Chi pi-gen NoType
`χ_-_ = λ T t → Chi pi-gen (SomeType T) t

-- Delta
infixr 8 δ-_ δ_-_ `δ-_ `δ_-_
pattern δ-_ t = Delta _ NoType t
pattern δ_-_ T t = Delta _ (SomeType T) t
`δ-_ = Delta pi-gen NoType
`δ_-_ = λ T t → Delta pi-gen (SomeType T) t

-- Epsilon
infixr 8 ε_ εl_ εr_ ε-_ εl-_ εr-_ `ε_ `εl_ `εr_ `ε-_ `εl-_ `εr-_
pattern ε_ t = Epsilon _ Both ff t
pattern εl_ t = Epsilon _ Left ff t
pattern εr_ t = Epsilon _ Right ff t
pattern ε-_ t = Epsilon _ Both tt t
pattern εl-_ t = Epsilon _ Left tt t
pattern εr-_ t = Epsilon _ Right tt t
`ε_ = Epsilon pi-gen Both ff
`εl_ = Epsilon pi-gen Left ff
`εr_ = Epsilon pi-gen Right ff
`ε-_ = Epsilon pi-gen Both tt
`εl-_ = Epsilon pi-gen Left tt
`εr-_ = Epsilon pi-gen Right tt

-- Hole
pattern ● = Hole _
`● = Hole pi-gen

-- IotaPair
pattern [_`,_] t₁ t₂ = IotaPair _ t₁ t₂ NoGuide _
pattern [_`,_*_₊_] t₁ t₂ x T = IotaPair _ t₁ t₂ (Guide _ x T) _ -- "₊" = "\_+"
`[_`,_] = λ t₁ t₂ → IotaPair pi-gen t₁ t₂ NoGuide pi-gen
`[_`,_*_₊_] = λ t₁ t₂ x T → IotaPair pi-gen t₁ t₂ (Guide pi-gen x T) pi-gen

-- IotaProj
infixl 5 _₊1 _₊2 _₊#_ _`₊1 _`₊2 _`₊#_
pattern _₊1 t = IotaProj t "1" _
pattern _₊2 t = IotaProj t "2" _
pattern _₊#_ t n = IotaProj t n _
_`₊1 = λ t → IotaProj t "1" pi-gen
_`₊2 = λ t → IotaProj t "2" pi-gen
_`₊#_ = λ t n → IotaProj t n pi-gen

-- Lam
infixr 4 λ`_₊_ λ`_:ₜ_₊_ λ`_:ₖ_₊_ Λ_₊_ Λ_:ₜ_₊_ Λ_:ₖ_₊_ `λ_₊_ `λ_:ₜ_₊_ `λ_:ₖ_₊_ `Λ_₊_ `Λ_:ₜ_₊_ `Λ_:ₖ_₊_
pattern λ`_₊_ x t = Lam _ NotErased _ x NoClass t
pattern λ`_:ₜ_₊_ x T t = Lam _ NotErased _ x (SomeClass (Tkt T)) t
pattern λ`_:ₖ_₊_ x k t = Lam _ NotErased _ x (SomeClass (Tkk k)) t
pattern Λ_₊_ x t = Lam _ Erased _ x NoClass t
pattern Λ_:ₜ_₊_ x T t = Lam _ Erased _ x (SomeClass (Tkt T)) t
pattern Λ_:ₖ_₊_ x k t = Lam _ Erased _ x (SomeClass (Tkk k)) t
`λ_₊_ = λ x t → Lam pi-gen NotErased pi-gen x NoClass t
`λ_:ₜ_₊_ = λ x T t → Lam pi-gen NotErased pi-gen x (SomeClass (Tkt T)) t
`λ_:ₖ_₊_ = λ x k t → Lam pi-gen NotErased pi-gen x (SomeClass (Tkk k)) t
`Λ_₊_ = λ x t → Lam pi-gen Erased pi-gen x NoClass t
`Λ_:ₜ_₊_ = λ x T t → Lam pi-gen Erased pi-gen x (SomeClass (Tkt T)) t
`Λ_:ₖ_₊_ = λ x k t → Lam pi-gen Erased pi-gen x (SomeClass (Tkk k)) t

-- Let
infixr 8 [_`=_]-_ [_:ₜ_`=_]-_ [_:ₖ_`=_]-_ -[_`=_]-_ -[_:ₜ_`=_]-_ -[_:ₖ_`=_]-_ `[_`=_]-_ `[_:ₜ_`=_]-_ `[_:ₖ_`=_]-_ `-[_`=_]-_ `-[_:ₜ_`=_]-_ `-[_:ₖ_`=_]-_
pattern [_`=_]-_ x t t' = Let _ NotErased (DefTerm _ x NoType t _) t'
pattern [_:ₜ_`=_]-_ x T t t' = Let _ NotErased (DefTerm _ x (SomeType T) t _) t'
pattern [_:ₖ_`=_]-_ x k T t' = Let _ NotErased (DefType _ x k T _) t'
pattern -[_`=_]-_ x t t' = Let _ Erased (DefTerm _ x NoType t _) t'
pattern -[_:ₜ_`=_]-_ x T t t' = Let _ Erased (DefTerm _ x (SomeType T) t _) t'
pattern -[_:ₖ_`=_]-_ x k T t' = Let _ Erased (DefType _ x k T _) t'
`[_`=_]-_ = λ x t t' → Let pi-gen NotErased (DefTerm pi-gen x NoType t) t'
`[_:ₜ_`=_]-_ = λ x T t t' → Let pi-gen NotErased (DefTerm pi-gen x (SomeType T) t) t'
`[_:ₖ_`=_]-_ = λ x k T t' → Let pi-gen NotErased (DefType pi-gen x k T) t'
`-[_`=_]-_ = λ x t t' → Let pi-gen Erased (DefTerm pi-gen x NoType t) t'
`-[_:ₜ_`=_]-_ = λ x T t t' → Let pi-gen Erased (DefTerm pi-gen x (SomeType T) t) t'
`-[_:ₖ_`=_]-_ = λ x k T t' → Let pi-gen Erased (DefType pi-gen x k T) t'


-- Open
infixr 8 open`_-_ `open_-_ close`_-_ `close_-_
pattern open`_-_ x t = Open _ OpacTrans _ x t
pattern close`_-_ x t = Open _ OpacOpaque _ x t
`open_-_ = Open pi-gen OpacTrans pi-gen
`close_-_ = Open pi-gen OpacOpaque pi-gen

--Parens
infix 4 ⦅_⦆ `⦅_⦆
pattern ⦅_⦆ t = Parens _ t _
`⦅_⦆ = λ t → Parens pi-gen t pi-gen


-- Phi
infix 8 φ_-_[_] `φ_-_[_]
pattern φ_-_[_] eq t₁ t₂ = Phi _ eq t₁ t₂ _
`φ_-_[_] = λ eq t₁ t₂ → Phi pi-gen eq t₁ t₂ pi-gen

-- Rho
infixr 8 ρ_-_ ρ<_>_-_ ρ_*_₊_-_ ρ<_>_*_₊_-_ ρ+_-_ ρ+<_>_-_ ρ+_*_₊_-_ ρ+<_>_*_₊_-_ `ρ_-_ `ρ<_>_-_ `ρ_*_₊_-_ `ρ<_>_*_₊_-_ `ρ+_-_ `ρ+<_>_-_ `ρ+_*_₊_-_ `ρ+<_>_*_₊_-_
pattern ρ_-_ t t' = Rho _ ff NoNums t NoGuide t'
pattern ρ<_>_-_ ns t t' = Rho _ ff (SomeNums ns) t NoGuide t'
pattern ρ_*_₊_-_ t x T t' = Rho _ ff NoNums t (Guide _ x T) t'
pattern ρ<_>_*_₊_-_ ns t x T t' = Rho _ ff (SomeNums ns) t (Guide _ x T) t'
pattern ρ+_-_ t t' = Rho _ tt NoNums t NoGuide t'
pattern ρ+<_>_-_ ns t t' = Rho _ tt (SomeNums ns) t NoGuide t'
pattern ρ+_*_₊_-_ t x T t' = Rho _ tt NoNums t (Guide _ x T) t'
pattern ρ+<_>_*_₊_-_ ns t x T t' = Rho _ tt (SomeNums ns) t (Guide _ x T) t'
`ρ_-_ = λ t t' → Rho pi-gen ff NoNums t NoGuide t'
`ρ<_>_-_ = λ ns t t' → Rho pi-gen ff (SomeNums ns) t NoGuide t'
`ρ_*_₊_-_ = λ t x T t' → Rho pi-gen ff NoNums t (Guide pi-gen x T) t'
`ρ<_>_*_₊_-_ = λ ns t x T t' → Rho pi-gen ff (SomeNums ns) t (Guide pi-gen x T) t'
`ρ+_-_ = λ t t' → Rho pi-gen tt NoNums t NoGuide t'
`ρ+<_>_-_ = λ ns t t' → Rho pi-gen tt (SomeNums ns) t NoGuide t'
`ρ+_*_₊_-_ = λ t x T t' → Rho pi-gen tt NoNums t (Guide pi-gen x T) t'
`ρ+<_>_*_₊_-_ = λ ns t x T t' → Rho pi-gen tt (SomeNums ns) t (Guide pi-gen x T) t'

-- Sigma
infixr 9 ς_ `ς_
pattern ς_ t = Sigma _ t
`ς_ = Sigma pi-gen


-- Theta
infix 9 θ_`_ θ+_`_ θ<_>_`_ `θ_`_ `θ+_`_ `θ<_>_`_
pattern θ_`_ t ts = Theta _ Abstract t ts
pattern θ+_`_ t ts = Theta _ AbstractEq t ts
pattern θ<_>_`_ vs t ts = Theta _ (AbstractVars vs) t ts
`θ_`_ = λ t ts → Theta pi-gen Abstract t ts
`θ+_`_ = λ t ts → Theta pi-gen AbstractEq t ts
`θ<_>_`_ = λ vs t ts → Theta pi-gen (AbstractVars vs) t ts

-- Mu
infix 9 μ_₊_[_] μ_₊_*_[_] `μ_₊_[_] `μ_₊_*_[_]
pattern μ_₊_[_] x t ms = Mu _ _ x t NoType _ ms _
pattern μ_₊_*_[_] x t T ms = Mu _ _ x t (SomeType T) _ ms _
`μ_₊_[_] = λ x t ms → Mu pi-gen pi-gen x t NoType pi-gen ms pi-gen
`μ_₊_*_[_] = λ x t T ms → Mu pi-gen pi-gen x t (SomeType T) pi-gen ms pi-gen

-- Mu'
infix 9 μ'_[_] μ'_*_[_] μ'<_>_[_] μ'<_>_*_[_] `μ'_[_] `μ'_*_[_] `μ'_[_] `μ'_*_[_]
pattern μ'_[_] t ms = Mu' _ NoTerm t NoType _ ms _
pattern μ'_*_[_] t T ms = Mu' _ NoTerm t (SomeType T) _ ms _
pattern μ'<_>_[_] t t' ms = Mu' _ (SomeTerm t) t' NoType _ ms _
pattern μ'<_>_*_[_] t t' T ms = Mu' _ (SomeTerm t) t' (SomeType T) _ ms _
`μ'_[_] = λ t ms → Mu' pi-gen NoTerm t NoType pi-gen ms pi-gen
`μ'_*_[_] = λ t T ms → Mu' pi-gen NoTerm t (SomeType T) pi-gen ms pi-gen
`μ'<_>_[_] = λ t t' ms → Mu' pi-gen (SomeTerm t pi-gen) t' NoType pi-gen ms pi-gen
`μ'<_>_*_[_] = λ t t' T ms → Mu' pi-gen (SomeTerm t pi-gen) t' (SomeType T) pi-gen ms pi-gen

-- Var
infixr 11 vₓ_ `vₓ_
pattern vₓ_ x = Var _ x
`vₓ_ = Var pi-gen



-- Abs
infixr 5 ∀`_:ₜ_₊_ ∀`_:ₖ_₊_ Π_:ₜ_₊_ Π_:ₖ_₊_ `∀_:ₜ_₊_ `∀_:ₖ_₊_ `Π_:ₜ_₊_ `Π_:ₖ_₊_
pattern ∀`_:ₜ_₊_ x T T' = Abs _ All _ x (Tkt T) T'
pattern ∀`_:ₖ_₊_ x k T = Abs _ All _ x (Tkk k) T
pattern Π_:ₜ_₊_ x T T' = Abs _ Pi _ x (Tkt T) T'
pattern Π_:ₖ_₊_ x k T = Abs _ Pi _ x (Tkk k) T
`∀_:ₜ_₊_ = λ x T T' → Abs pi-gen All pi-gen x (Tkt T) T'
`∀_:ₖ_₊_ = λ x k T → Abs pi-gen All pi-gen x (Tkk k) T
`Π_:ₜ_₊_ = λ x T T' → Abs pi-gen Pi pi-gen x (Tkt T) T'
`Π_:ₖ_₊_ = λ x k T → Abs pi-gen Pi pi-gen x (Tkk k) T



-- Iota
infix 4 ι_:ₜ_₊_ `ι_:ₜ_₊_
pattern ι_:ₜ_₊_ x T T' = Iota _ _ x T T'
`ι_:ₜ_₊_ = Iota pi-gen pi-gen

-- Lft
infix 4 ↑_₊_:ₗ_ `↑_₊_:ₗ_
pattern ↑_₊_:ₗ_ X t lT = Lft _ _ X t lT
`↑_₊_:ₗ_ = Lft pi-gen pi-gen

-- NoSpans
infix 4 [^_^] `[^_^]
pattern [^_^] T = NoSpans T _
`[^_^] = λ T → NoSpans T pi-gen

-- TpLet
infixr 5 [_`=_]ₜ-_ [_:ₜ_`=_]ₜ-_ [_:ₖ_`=_]ₜ-_ `[_`=_]ₜ-_ `[_:ₜ_`=_]ₜ-_ `[_:ₖ_`=_]ₜ-_
pattern [_`=_]ₜ-_ x t t' = TpLet _ (DefTerm _ x NoType t _) t'
pattern [_:ₜ_`=_]ₜ-_ x T t t' = TpLet _ (DefTerm _ x (SomeType T) t _) t'
pattern [_:ₖ_`=_]ₜ-_ x k T t' = TpLet _ (DefType _ x k T _) t'
`[_`=_]ₜ-_ = λ x t t' → TpLet pi-gen (DefTerm pi-gen x NoType t) t'
`[_:ₜ_`=_]ₜ-_ = λ x T t t' → TpLet pi-gen (DefTerm pi-gen x (SomeType T) t) t'
`[_:ₖ_`=_]ₜ-_ = λ x k T t' → TpLet pi-gen (DefType pi-gen x k T) t'


-- TpApp, TpAppt
infixl 10 _·ₜ_ _`ₜ_
-- Pattern and constructor
pattern _·ₜ_ T T' = TpApp T T'
pattern _`ₜ_ T t = TpAppt T t

-- TpArrow
infixr 5 _➔_ _➾_  -- "➔" = "\r" (↕ 5, ↔ 1), "➾" = "\r" (↕ 7, ↔ 8)
pattern _➔_ T T' = TpArrow T NotErased T'
pattern _➾_ T T' = TpArrow T Erased T'

-- TpEq
infix 4 [_≃_] `[_≃_]
pattern [_≃_] t₁ t₂ = TpEq _ t₁ t₂ _
`[_≃_] = λ t₁ t₂ → TpEq pi-gen t₁ t₂ pi-gen

-- TpHole
pattern ●ₜ = TpHole _
`●ₜ = TpHole pi-gen

-- TpLambda
infixr 4 λₜ_:ₜ_₊_ λₜ_:ₖ_₊_ `λₜ_:ₜ_₊_ `λₜ_:ₖ_₊_
pattern λₜ_:ₜ_₊_ x T T' = TpLambda _ _ x (Tkt T) T'
pattern λₜ_:ₖ_₊_ x k T = TpLambda _ _ x (Tkk k) T
`λₜ_:ₜ_₊_ = λ x T T' → TpLambda pi-gen pi-gen x (Tkt T) T'
`λₜ_:ₖ_₊_ = λ x k T → TpLambda pi-gen pi-gen x (Tkk k) T

-- TpParens
infix 4 ⦅_⦆ₜ `⦅_⦆ₜ
pattern ⦅_⦆ₜ T = TpParens _ T _
`⦅_⦆ₜ = λ T → TpParens pi-gen T pi-gen

-- TpVar
infix 11 Vₓ_ `Vₓ_
pattern Vₓ_ x = TpVar _ x
`Vₓ_ = TpVar pi-gen



-- KndArrow : kind → kind → kind

-- KndParens : posinfo → kind → posinfo → kind
infix 4 ⦅_⦆ₖ `⦅_⦆ₖ
pattern ⦅_⦆ₖ k = KndParens _ k _
`⦅_⦆ₖ = λ k → KndParens pi-gen k pi-gen

-- KndPi : posinfo → posinfo → bvar → tk → kind → kind

-- KndTpArrow : type → kind → kind

-- KndVar
infix 11 κ_`_ `κ_`_
pattern κ_`_ x as = KndVar _ x as
`κ_`_ = KndVar pi-gen

-- Star
pattern ★ = Star _
`★ = Star pi-gen
