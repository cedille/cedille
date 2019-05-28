----------------------------------------------------------------------------------
-- Types for parse trees
----------------------------------------------------------------------------------

module cedille-types where

open import lib
-- open import parse-tree
open import general-util

{-# FOREIGN GHC import qualified CedilleTypes #-}

mutual
  posinfo = string
  var = string
  num = string
  erased? = 𝔹
  NotErased = ff
  Erased = tt
  maybeMinus = 𝔹
  imports = 𝕃 imprt
  params = 𝕃 param
  ex-params = 𝕃 ex-param
  cmds = 𝕃 cmd
  ex-ctrs = 𝕃 ex-ctr
  ctrs = 𝕃 ctr
  args = 𝕃 arg
  ex-args = 𝕃 ex-arg
  opacity = 𝔹
  opacity-open = tt
  opacity-closed = ff
  cases = 𝕃 case
  ex-cases = 𝕃 ex-case
  left-right = maybe 𝔹
  rho-hnf = 𝔹
  opt-public = 𝔹
  is-mu = maybe term ⊎ var
  iota-num = 𝔹
  ι1 = ff
  ι2 = tt
  case-args = 𝕃 case-arg


  data ctr : Set where
    Ctr : var → type → ctr

  data param : Set where
    Param : erased? → var → tpkd → param
  
  data arg : Set where
    TmArg : erased? → term → arg
    TpArg : type → arg

--  {-# NO_POSITIVITY_CHECK #-}
  data term : Set where
    App : term → erased? → term → term
    AppTp : term → type → term
    Beta : maybe term → maybe term → term
    Delta : type → term → term
    Hole : posinfo → term
    IotaPair : term → term → var → type → term
    IotaProj : term → iota-num → term
    Lam : erased? → var → maybe tpkd → term → term
    LetTm : erased? → var → maybe type → term → term → term
    LetTp : var → kind → type → term → term
    Open : opacity → var → term → term
    Phi : term → term → term → term
    Rho : term → var → type → term → term
    Sigma : term → term
    Mu : is-mu → term → maybe type → (ex-is-mu → ex-tm → maybe ex-tp → ex-cases → ex-tm) → cases → term
    Var : var → term

  data case : Set where
    Case : var → case-args → term → case

  data tpkd : Set where
    Tkt : type → tpkd
    Tkk : kind → tpkd
  
  data type : Set where
    TpAbs : erased? → var → tpkd → type → type
    TpIota : var → type → type → type
    TpApp : type → type → type
    TpAppt : type → term → type
    TpEq : term → term → type
    TpHole : posinfo → type
    TpLam : var → tpkd → type → type
    TpVar : var → type
  
  data kind : Set where
    KdStar : kind
    KdAbs : var → tpkd → kind → kind


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
  pattern `λ_`:_`,_ x T t = Lam ff x (just (Tkt T)) t
  pattern `λ_`:'_`,_ x k t = Lam ff x (just (Tkk k)) t
  pattern `Λ_`,_ x t = Lam tt x nothing t
  pattern `Λ_`:_`,_ x T t = Lam tt x (just (Tkt T)) t
  pattern `Λ_`:'_`,_ x k t = Lam tt x (just (Tkk k)) t
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
  pattern _`_ t t' = App t ff t'
  pattern _`-_ t t' = App t tt t'
  pattern _`·_ t T = AppTp t T


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
  pattern `Π_`:_`,_ x T T' = TpAbs ff x (Tkt T) T'
  pattern `Π_`:'_`,_ x k T = TpAbs ff x (Tkk k) T
  pattern `∀_`:_`,_ x T T' = TpAbs tt x (Tkt T) T'
  pattern `∀_`:'_`,_ x k T = TpAbs tt x (Tkk k) T
  pattern `λ'_`:_`,_ x T T' = TpLam x (Tkt T) T'
  pattern `λ'_`:'_`,_ x k T = TpLam x (Tkk k) T
  pattern `ι_`:_`,_ x T₁ T₂ = TpIota x T₁ T₂
  
  infixl 16 _``_ _``·_
  pattern _``_ T t = TpAppt T t
  pattern _``·_ T T' = TpApp T T'

  infix 16 `[_≃_]
  pattern `[_≃_] t₁ t₂ = TpEq t₁ t₂
  pattern _ₓ_ x as = TpVar x as
  pattern ● {pi} = TpHole pi

  ●' : ∀ {b} → if b then term else type
  ●' {tt} = ● {"missing"}
  ●' {ff} = ● {"missing"}

  infixr 17 `Π'_`:_`,_ `Π'_`:'_`,_
  pattern `Π'_`:_`,_ x T k = KdAbs x (Tkt T) k
  pattern `Π'_`:'_`,_ x k k' = KdAbs x (Tkk k) k'
  
  pattern ★ = KdStar

  infixr 20 `|_`_➔_ -- \r (05 - 1)
  pattern `|_`_➔_ x xs t = Case x xs t

  data file : Set where
    Module : imports → posinfo → posinfo → var → ex-params → cmds → posinfo → file
  
  data cmd : Set where
    CmdKind : posinfo → var → ex-params → ex-kd → posinfo → cmd
    CmdDef : opacity → def → posinfo → cmd
    CmdData : def-datatype → posinfo → cmd
    CmdImport : imprt → cmd

  data def-datatype : Set where
    DefDatatype : posinfo → posinfo → var → ex-params → ex-kd → ex-ctrs → def-datatype
  
  data import-as : Set where
    ImportAs : posinfo → var → import-as
  
  data imprt : Set where
    Import : posinfo → opt-public → posinfo → filepath → maybe import-as → ex-args → posinfo → imprt

  data ex-param : Set where
    ExParam : posinfo → erased? → posinfo → var → ex-tk → posinfo → ex-param  
  
  data ex-ctr : Set where
    ExCtr : posinfo → var → ex-tp → ex-ctr
    
  data ex-arg : Set where
    ExTmArg : erased? → ex-tm → ex-arg
    ExTpArg : ex-tp → ex-arg
    
  data case-arg-sym : Set where
    CaseArgTm {-  x -} : case-arg-sym
    CaseArgEr {- -x -} : case-arg-sym
    CaseArgTp {- ·x -} : case-arg-sym
  
  data case-arg : Set where
    CaseArg : case-arg-sym → var → case-arg
    
  data lterm : Set where
    Lterm : erased? → ex-tm → lterm
  
  data theta : Set where
    Abstract : theta
    AbstractEq : theta
    AbstractVars : 𝕃 var → theta
  
  data def : Set where
    DefTerm : posinfo → var → maybe ex-tp → ex-tm → def
    DefType : posinfo → var → ex-kd → ex-tp → def
  
  data ex-guide : Set where
    ExGuide : posinfo → var → ex-tp → ex-guide
  
  data ex-case : Set where
    ExCase : posinfo → var → 𝕃 ex-case-arg → ex-tm → ex-case
  
  data ex-case-arg : Set where
    ExCaseArg : case-arg-sym → posinfo → var → ex-case-arg
  
  data ex-tk : Set where
    ExTkt : ex-tp → ex-tk
    ExTkk : ex-kd → ex-tk
  
  data ex-tp : Set where
    ExTpAbs : posinfo → erased? → posinfo → var → ex-tk → ex-tp → ex-tp
    ExTpIota : posinfo → posinfo → var → ex-tp → ex-tp → ex-tp
    ExTpNoSpans : ex-tp → posinfo → ex-tp
    ExTpLet : posinfo → def → ex-tp → ex-tp
    ExTpApp : ex-tp → ex-tp → ex-tp
    ExTpAppt : ex-tp → ex-tm → ex-tp
    ExTpArrow : ex-tp → erased? → ex-tp → ex-tp
    ExTpEq : posinfo → ex-tm → ex-tm → posinfo → ex-tp
    ExTpHole : posinfo → ex-tp
    ExTpLam : posinfo → posinfo → var → ex-tk → ex-tp → ex-tp
    ExTpParens : posinfo → ex-tp → posinfo → ex-tp
    ExTpVar : posinfo → var → ex-tp
  
  data pos-tm : Set where
    PosTm : ex-tm → posinfo → pos-tm
  
  data ex-is-mu : Set where
    ExIsMu : posinfo → var → ex-is-mu
    ExIsMu' : maybe ex-tm → ex-is-mu
  
  data ex-tm : Set where
    ExApp : ex-tm → erased? → ex-tm → ex-tm
    ExAppTp : ex-tm → ex-tp → ex-tm
    ExBeta : posinfo → maybe pos-tm → maybe pos-tm → ex-tm
    ExChi : posinfo → maybe ex-tp → ex-tm → ex-tm
    ExDelta : posinfo → maybe ex-tp → ex-tm → ex-tm
    ExEpsilon : posinfo → left-right → maybeMinus → ex-tm → ex-tm
    ExHole : posinfo → ex-tm
    ExIotaPair : posinfo → ex-tm → ex-tm → maybe ex-guide → posinfo → ex-tm
    ExIotaProj : ex-tm → num → posinfo → ex-tm
    ExLam : posinfo → erased? → posinfo → var → maybe ex-tk → ex-tm → ex-tm
    ExLet : posinfo → erased? → def → ex-tm → ex-tm
    ExOpen : posinfo → opacity → posinfo → var → ex-tm → ex-tm
    ExParens : posinfo → ex-tm → posinfo → ex-tm
    ExPhi : posinfo → ex-tm → ex-tm → ex-tm → posinfo → ex-tm
    ExRho : posinfo → rho-hnf → maybe (𝕃 num) → ex-tm → maybe ex-guide → ex-tm → ex-tm
    ExSigma : posinfo → ex-tm → ex-tm
    ExTheta : posinfo → theta → ex-tm → 𝕃 lterm → ex-tm
    ExMu : posinfo → ex-is-mu → ex-tm → maybe ex-tp → posinfo → ex-cases → posinfo → ex-tm
    ExVar : posinfo → var → ex-tm
  
  data ex-kd : Set where
    ExKdArrow : ex-tk → ex-kd → ex-kd
    ExKdParens : posinfo → ex-kd → posinfo → ex-kd
    ExKdAbs : posinfo → posinfo → var → ex-tk → ex-kd → ex-kd
    ExKdVar : posinfo → var → ex-args → ex-kd
    ExKdStar : posinfo → ex-kd
  
{-# COMPILE GHC ex-param = data CedilleTypes.Param (CedilleTypes.Param) #-}
{-# COMPILE GHC file = data CedilleTypes.File (CedilleTypes.Module) #-}
{-# COMPILE GHC cmd = data CedilleTypes.Cmd (CedilleTypes.CmdKind | CedilleTypes.CmdDef | CedilleTypes.CmdData | CedilleTypes.CmdImport) #-}
{-# COMPILE GHC ex-ctr = data CedilleTypes.Ctr (CedilleTypes.Ctr) #-}
{-# COMPILE GHC def-datatype = data CedilleTypes.DefDatatype (CedilleTypes.DefDatatype) #-}
{-# COMPILE GHC import-as = data CedilleTypes.ImportAs (CedilleTypes.ImportAs) #-}
{-# COMPILE GHC imprt = data CedilleTypes.Imprt (CedilleTypes.Import) #-}
{-# COMPILE GHC case-arg-sym = data CedilleTypes.CaseArgSym (CedilleTypes.CaseArgTm | CedilleTypes.CaseArgEr | CedilleTypes.CaseArgTp) #-}
{-# COMPILE GHC case-arg = data CedilleTypes.CaseArg (CedilleTypes.CaseArg) #-}

{-# COMPILE GHC lterm = data CedilleTypes.Lterm (CedilleTypes.Lterm) #-}
{-# COMPILE GHC theta = data CedilleTypes.Theta (CedilleTypes.Abstract | CedilleTypes.AbstractEq | CedilleTypes.AbstractVars) #-}
{-# COMPILE GHC def = data CedilleTypes.Def (CedilleTypes.DefTerm | CedilleTypes.DefType) #-}
{-# COMPILE GHC ex-guide = data CedilleTypes.Guide (CedilleTypes.Guide) #-}
{-# COMPILE GHC ex-case = data CedilleTypes.Case (CedilleTypes.Case) #-}
{-# COMPILE GHC ex-case-arg = data CedilleTypes.CaseArg (CedilleTypes.CaseArg) #-}
{-# COMPILE GHC ex-tk = data CedilleTypes.Tk (CedilleTypes.Tkt | CedilleTypes.Tkk) #-}
{-# COMPILE GHC ex-tp = data CedilleTypes.Type (CedilleTypes.TpAbs | CedilleTypes.TpIota | CedilleTypes.TpNoSpans | CedilleTypes.TpLet | CedilleTypes.TpApp | CedilleTypes.TpAppt | CedilleTypes.TpArrow | CedilleTypes.TpEq | CedilleTypes.TpHole | CedilleTypes.TpLam | CedilleTypes.TpParens | CedilleTypes.TpVar) #-}
{-# COMPILE GHC pos-tm = data CedilleTypes.PosTerm (CedilleTypes.PosTerm) #-}
{-# COMPILE GHC ex-is-mu = data CedilleTypes.IsMu (CedilleTypes.IsMu | CedilleTypes.IsMu') #-}
{-# COMPILE GHC ex-tm = data CedilleTypes.Term (CedilleTypes.App | CedilleTypes.AppTp | CedilleTypes.Beta | CedilleTypes.Chi | CedilleTypes.Delta | CedilleTypes.Epsilon | CedilleTypes.Hole | CedilleTypes.IotaPair | CedilleTypes.IotaProj | CedilleTypes.Lam | CedilleTypes.Let | CedilleTypes.Open | CedilleTypes.Parens | CedilleTypes.Phi | CedilleTypes.Rho | CedilleTypes.Sigma | CedilleTypes.Theta | CedilleTypes.Mu | CedilleTypes.Var) #-}
{-# COMPILE GHC ex-kd = data CedilleTypes.Kd (CedilleTypes.KdArrow | CedilleTypes.KdParens | CedilleTypes.KdAbs | CedilleTypes.KdVar | CedilleTypes.KdStar) #-}
