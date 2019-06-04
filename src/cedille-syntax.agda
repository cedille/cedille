module cedille-syntax where
--open import lib
open import string
open import bool
open import unit
open import syntax-util
open import general-util
open import cedille-types
open import erase

  -- Terms:
  -- 1—Lam, Let, Er. Let, Open, Close, Rho, Phi, Delta (11)
  -- 2—App, Er. App, Tp. App (12)
  -- 3—Beta, Sigma (13)
  -- 4—Var, IotaProj, IotaPair, Mu, Mu', Hole (14)

  infixr 11
    `λ_`,_   `λ_`:_`,_ -- \Gl or \lambda or \lamda
    `Λ_`,_   `Λ_`:_`,_ -- \GL or \Lambda or \Lamda
    `[_`:_`=_]-_   `[_`=_]-_
    `-[_`:_`=_]-_   `-[_`=_]-_
    `open_-_   `close_-_
    `ρ_`:_`,_-_ -- \Gr or \rho
    `δ_-_ -- \Gd or \delta
  infix 11 `φ_-_[_] -- \G or \phi
  pattern `λ_`,_ x t = Lam ff x nothing t
  pattern `λ_`:_`,_ x T t = Lam ff x (just (inj₁ T)) t
  pattern `λ_`:'_`,_ x k t = Lam ff x (just (inj₂ k)) t
  pattern `Λ_`,_ x t = Lam tt x nothing t
  pattern `Λ_`:_`,_ x T t = Lam tt x (just (inj₁ T)) t
  pattern `Λ_`:'_`,_ x k t = Lam tt x (just (inj₂ k)) t
  pattern `[_`:_`=_]-_ x T t t' = LetTm ff x (just T) t t'
  pattern `[_`:'_`=_]-_ x k T t = LetTp x k T t
  pattern `[_`=_]-_ x t t' = LetTm ff x nothing t t'
  pattern `-[_`:_`=_]-_ x T t t' = LetTm tt x (just T) t t'
  pattern `-[_`:'_`=_]-_ x k T t = LetTp x k T t
  pattern `-[_`=_]-_ x t t' = LetTm tt x nothing t t'
  pattern `open_-_ x t = Open tt x t
  pattern `close_-_ x t = Open ff x t
  pattern `ρ_`:_`,_-_ tₑ x T t = Rho tₑ x T t
  pattern `δ_-_ T t = Delta T t
  pattern `φ_-_[_] tₑ t₁ t₂ = Phi tₑ t₁ t₂

  infixl 12 _`_ _`-_ _`·_ -- \cdot
  pattern _`_ t t' = App t t'
  pattern _`-_ t t' = AppE t (inj₁ t')
  pattern _`·_ t T = AppE t (inj₂ T)


  infix 13 `β<_> `β'<_> -- \Gb or \beta
  infixr 13 `ς_ -- \varsigma  
  pattern `β = Beta nothing nothing
  pattern `β<_> t = Beta (just t) nothing
  pattern `β'{t} = Beta nothing (just t)
  pattern `β'<_> t {t'} = Beta (just t) (just t')
  pattern `ς_ t = Sigma t

  infix 14
    ₓ_ -- \_x
    `μ_`,_`
    `μ'_`
    `μ_`,_`:_`
    `μ'_`:_` -- \Gm or \mu
  infixl 14 _`1 _`2
  infix 14 `[_`,_`:_`,_] ● -- \ci
  pattern ₓ_ x = Var x
  pattern ₓ_ X = TpVar X
  pattern _`1 t = IotaProj t ff
  pattern _`2 t = IotaProj t tt
  pattern `[_`,_`:_`,_] t₁ t₂ x Tₓ = IotaPair t₁ t₂ x Tₓ
  pattern `μ_`,_` x t {cs} = Mu (inj₂ x) t nothing cs
  pattern `μ'_` t {cs} = Mu (inj₁ nothing) t nothing cs
  pattern `μ_`,_`:_` x t T {cs} = Mu (inj₂ x) t (just T) cs
  pattern `μ'_`:_` t T {cs} = Mu (inj₁ nothing) t (just T) cs
  pattern ● {pi} = Hole pi
    
  infixr 15
    `Π_`:_`,_ `Π_`:'_`,_
    `∀_`:_`,_ `∀_`:'_`,_
    `λ'_`:_`,_ `λ'_`:'_`,_
    `ι_`:_`,_
  pattern `Π_`:_`,_ x T T' = TpAbs ff x (inj₁ T) T'
  pattern `Π_`:'_`,_ x k T = TpAbs ff x (inj₂ k) T
  pattern `∀_`:_`,_ x T T' = TpAbs tt x (inj₁ T) T'
  pattern `∀_`:'_`,_ x k T = TpAbs tt x (inj₂ k) T
  pattern `λ'_`:_`,_ x T T' = TpLam x (inj₁ T) T'
  pattern `λ'_`:'_`,_ x k T = TpLam x (inj₂ k) T
  pattern `ι_`:_`,_ x T₁ T₂ = TpIota x T₁ T₂
  
  infixl 16 _``_ _``·_
  pattern _``_ T t = TpApp T (inj₁ t)
  pattern _``·_ T T' = TpApp T (inj₂ T')

  infix 16 `[_≃_]
  pattern `[_≃_] t₁ t₂ = TpEq t₁ t₂
  pattern _ₓ_ x as = TpVar x as
  pattern ● {pi} = TpHole pi

  ●' : ∀ {b} → if b then term else type
  ●' {tt} = ● {"missing"}
  ●' {ff} = ● {"missing"}

  infixr 17 `Π'_`:_`,_ `Π'_`:'_`,_
  pattern `Π'_`:_`,_ x T k = KdAbs x (inj₁ T) k
  pattern `Π'_`:'_`,_ x k k' = KdAbs x (inj₂ k) k'
  
  pattern ★ = KdStar

  infixr 20 `|_`_➔_ -- \r (05 - 1)
  pattern `|_`_➔_ x xs t = Case x xs t

