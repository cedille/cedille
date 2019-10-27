----------------------------------------------------------------------------------
-- Types for parse trees
----------------------------------------------------------------------------------

module cedille-types where

open import ial
-- open import parse-tree
open import general-util

{-# FOREIGN GHC import qualified CedilleTypes #-}

mutual
  posinfo = string
  var = string
  num = string
  erased? = 𝔹
  minus? = 𝔹
  imports = 𝕃 imprt
  ex-imports = 𝕃 ex-imprt
  params = 𝕃 param
  ex-params = 𝕃 ex-param
  ex-cmds = 𝕃 ex-cmd
  ex-ctrs = 𝕃 ex-ctr
  ctrs = 𝕃 ctr
  args = 𝕃 arg
  ex-args = 𝕃 ex-arg
  opacity = 𝔹
  cases = 𝕃 case
  ex-cases = 𝕃 ex-case
  left-right = maybe 𝔹
  rho-hnf = 𝔹
  opt-public = 𝔹
  is-mu = maybe term ⊎ var
  iota-num = 𝔹
  case-args = 𝕃 case-arg
  tmtp = term ⊎ type
  tpkd = type ⊎ kind
  arg = term ⊎ tmtp

  pattern Tkt T = inj₁ T
  pattern Tkk k = inj₂ k
  pattern Ttm t = inj₁ t
  pattern Ttp T = inj₂ T
  pattern Arg t = inj₁ t
  pattern ArgE tT = inj₂ tT
  pattern ArgTp T = ArgE (Ttp T)
  pattern ArgEr t = ArgE (Ttm t)
  pattern ι1 = ff
  pattern ι2 = tt
  pattern NotErased = ff
  pattern Erased = tt
  pattern opacity-open = tt
  pattern opacity-closed = ff
  pattern EpsHanf = tt
  pattern EpsHnf = ff
  pattern EpsLeft = just ff
  pattern EpsRight = just tt
  pattern EpsBoth = nothing
  pattern Public = tt
  pattern Private = ff

  ctr = var × type
  pattern Ctr x T = x , T

  data param : Set where
    Param : erased? → var → tpkd → param
  pattern ParamTp x k = Param _  x (Tkk k)
  pattern ParamTm x T = Param ff x (Tkt T)
  pattern ParamEr x T = Param tt x (Tkt T)


  data term : Set where
    App : term → term → term
    AppE : term → tmtp → term
    Beta : term → term → term
    Delta : (do-bohm? : maybe (term × term)) → (Tᵣ : type) → (contra : term) → term
    Hole : posinfo → term
    IotaPair : term → term → var → type → term
    IotaProj : term → iota-num → term
    Lam : erased? → var → maybe tpkd → term → term
    LetTm : erased? → var → maybe type → term → term → term
    LetTp : var → kind → type → term → term
    Phi : term → term → term → term
    Rho : term → var → type → term → term
    Sigma : term → term
    Mu : is-mu → term → maybe type → datatype-info → cases → term
    Var : var → term
  pattern AppTp t T = AppE t (Ttp T)
  pattern AppEr t t' = AppE t (Ttm t')

  data case : Set where
    Case : var → case-args → term → 𝕃 tmtp → case

  data type : Set where
    TpAbs : erased? → var → tpkd → type → type
    TpIota : var → type → type → type
    TpApp : type → tmtp → type
    TpEq : term → term → type
    TpHole : posinfo → type
    TpLam : var → tpkd → type → type
    TpVar : var → type
  pattern TpAppTp T T' = TpApp T (Ttp T')
  pattern TpAppTm T t = TpApp T (Ttm t)
  
  data kind : Set where
    KdStar : kind
    KdHole : posinfo → kind
    KdAbs : var → tpkd → kind → kind

  data case-arg : Set where
    CaseArg : erased? → var → maybe tpkd → case-arg

  data ex-file : Set where
    ExModule : ex-imports → posinfo → posinfo → var → ex-params → ex-cmds → posinfo → ex-file

  cmds = 𝕃 cmd

  data file : Set where
    Module : var → params → cmds → file

  indx : Set
  indx = var × tpkd
  pattern Index x tk = x , tk
  indices = 𝕃 indx

  record encoding-defs : Set where
    constructor mk-enc-defs
    inductive
    field
      ecs : cmds -- encoding
      gcs : cmds -- generated
      Cast : type
      cast-in : term
      cast-out : term
      cast-is : term
      Functor : type
      functor-in : term
      functor-out : term
      Fix : type
      fix-in : term
      fix-out : term
      lambek1 : term
      lambek2 : term
      fix-ind : term

  record encoded-defs : Set where
    constructor mk-encd-defs
    field
      Is/D : var
      is/D : var
      to/D : var
      TypeF/D : var
      IndF/D : var
      fmap/D :  var

  record datatype-info : Set where
    constructor mk-data-info
    inductive
    field
      name : var
      original : var
      asₚ : args
      asᵢ : 𝕃 tmtp
      ps : params
      kᵢ : kind
      k : kind
      cs : ctrs
      csₚₛ : ctrs
      eds : encoding-defs
      gds : encoded-defs


  data cmd : Set where
    CmdDefTerm : var → term → cmd
    CmdDefType : var → kind → type → cmd
    CmdDefKind : var → params → kind → cmd
    CmdDefData : encoding-defs → var → params → kind → ctrs → cmd
    CmdImport : imprt → cmd

  data imprt : Set where
    Import : opt-public → filepath → var → maybe var → args → imprt

  data ex-cmd : Set where
    ExCmdKind : posinfo → var → ex-params → ex-kd → posinfo → ex-cmd
    ExCmdDef : opacity → ex-def → posinfo → ex-cmd
    ExCmdData : def-datatype → posinfo → ex-cmd
    ExCmdImport : ex-imprt → ex-cmd

  data def-datatype : Set where
    DefDatatype : posinfo → posinfo → var → ex-params → ex-kd → ex-ctrs → def-datatype
  
  data import-as : Set where
    ImportAs : posinfo → var → import-as
  
  data ex-imprt : Set where
    ExImport : posinfo → opt-public → posinfo → filepath → maybe import-as → ex-args → posinfo → ex-imprt

  data ex-param : Set where
    ExParam : posinfo → erased? → posinfo → var → ex-tk → posinfo → ex-param  
  
  data ex-ctr : Set where
    ExCtr : posinfo → var → ex-tp → ex-ctr
    
  data ex-arg : Set where
    ExTmArg : erased? → ex-tm → ex-arg
    ExTpArg : ex-tp → ex-arg
    
  data lterm : Set where
    Lterm : erased? → ex-tm → lterm
  
  data theta : Set where
    Abstract : theta
    AbstractEq : theta
    AbstractVars : 𝕃 var → theta
  
  data ex-def : Set where
    ExDefTerm : posinfo → var → maybe ex-tp → ex-tm → ex-def
    ExDefType : posinfo → var → ex-kd → ex-tp → ex-def
  
  data ex-guide : Set where
    ExGuide : posinfo → var → ex-tp → ex-guide
  
  data ex-case : Set where
    ExCase : posinfo → var → ex-case-args → ex-tm → ex-case

  ex-case-args = 𝕃 ex-case-arg
  
  data ex-case-arg-sym : Set where
    ExCaseArgTm : ex-case-arg-sym
    ExCaseArgEr : ex-case-arg-sym
    ExCaseArgTp : ex-case-arg-sym

  data ex-case-arg : Set where
    ExCaseArg : ex-case-arg-sym → posinfo → var → ex-case-arg
  
  data ex-tk : Set where
    ExTkt : ex-tp → ex-tk
    ExTkk : ex-kd → ex-tk
  
  data ex-tp : Set where
    ExTpAbs : posinfo → erased? → posinfo → var → ex-tk → ex-tp → ex-tp
    ExTpIota : posinfo → posinfo → var → ex-tp → ex-tp → ex-tp
    ExTpNoSpans : ex-tp → posinfo → ex-tp
    ExTpLet : posinfo → ex-def → ex-tp → ex-tp
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
    ExEpsilon : posinfo → left-right → minus? → ex-tm → ex-tm
    ExHole : posinfo → ex-tm
    ExIotaPair : posinfo → ex-tm → ex-tm → maybe ex-guide → posinfo → ex-tm
    ExIotaProj : ex-tm → num → posinfo → ex-tm
    ExLam : posinfo → erased? → posinfo → var → maybe ex-tk → ex-tm → ex-tm
    ExLet : posinfo → erased? → ex-def → ex-tm → ex-tm
    ExOpen : posinfo → opacity → posinfo → var → ex-tm → ex-tm
    ExParens : posinfo → ex-tm → posinfo → ex-tm
    ExPhi : posinfo → ex-tm → ex-tm → ex-tm → posinfo → ex-tm
    ExRho : posinfo → rho-hnf → maybe (𝕃 num) → ex-tm → maybe ex-guide → ex-tm → ex-tm
    ExSigma : posinfo → ex-tm → ex-tm
    ExTheta : posinfo → theta → ex-tm → 𝕃 lterm → ex-tm
    ExMu : posinfo → ex-is-mu → ex-tm → maybe ex-tp → posinfo → ex-cases → posinfo → ex-tm
    ExVar : posinfo → var → ex-tm
  
  data ex-kd : Set where
    ExKdAbs : posinfo → posinfo → var → ex-tk → ex-kd → ex-kd
    ExKdArrow : ex-tk → ex-kd → ex-kd
    ExKdHole : posinfo → ex-kd
    ExKdParens : posinfo → ex-kd → posinfo → ex-kd
    ExKdStar : posinfo → ex-kd
    ExKdVar : posinfo → var → ex-args → ex-kd
  
{-# COMPILE GHC ex-param = data CedilleTypes.Param (CedilleTypes.Param) #-}
{-# COMPILE GHC ex-file = data CedilleTypes.File (CedilleTypes.Module) #-}
{-# COMPILE GHC ex-cmd = data CedilleTypes.Cmd (CedilleTypes.CmdKind | CedilleTypes.CmdDef | CedilleTypes.CmdData | CedilleTypes.CmdImport) #-}
{-# COMPILE GHC ex-ctr = data CedilleTypes.Ctr (CedilleTypes.Ctr) #-}
{-# COMPILE GHC ex-arg = data CedilleTypes.Arg (CedilleTypes.TermArg | CedilleTypes.TypeArg) #-}
{-# COMPILE GHC def-datatype = data CedilleTypes.DefDatatype (CedilleTypes.DefDatatype) #-}
{-# COMPILE GHC import-as = data CedilleTypes.ImportAs (CedilleTypes.ImportAs) #-}
{-# COMPILE GHC ex-imprt = data CedilleTypes.Imprt (CedilleTypes.Import) #-}
{-# COMPILE GHC ex-case-arg-sym = data CedilleTypes.CaseArgSym (CedilleTypes.CaseArgTm | CedilleTypes.CaseArgEr | CedilleTypes.CaseArgTp) #-}
--{-# COMPILE GHC case-arg = data CedilleTypes.CaseArg (CedilleTypes.CaseArg) #-}
{-# COMPILE GHC lterm = data CedilleTypes.Lterm (CedilleTypes.Lterm) #-}
{-# COMPILE GHC theta = data CedilleTypes.Theta (CedilleTypes.Abstract | CedilleTypes.AbstractEq | CedilleTypes.AbstractVars) #-}
{-# COMPILE GHC ex-def = data CedilleTypes.Def (CedilleTypes.DefTerm | CedilleTypes.DefType) #-}
{-# COMPILE GHC ex-guide = data CedilleTypes.Guide (CedilleTypes.Guide) #-}
{-# COMPILE GHC ex-case = data CedilleTypes.Case (CedilleTypes.Case) #-}
{-# COMPILE GHC ex-case-arg = data CedilleTypes.CaseArg (CedilleTypes.CaseArg) #-}
{-# COMPILE GHC ex-tk = data CedilleTypes.TpKd (CedilleTypes.Tkt | CedilleTypes.Tkk) #-}
{-# COMPILE GHC ex-tp = data CedilleTypes.Type (CedilleTypes.TpAbs | CedilleTypes.TpIota | CedilleTypes.TpNoSpans | CedilleTypes.TpLet | CedilleTypes.TpApp | CedilleTypes.TpAppt | CedilleTypes.TpArrow | CedilleTypes.TpEq | CedilleTypes.TpHole | CedilleTypes.TpLam | CedilleTypes.TpParens | CedilleTypes.TpVar) #-}
{-# COMPILE GHC pos-tm = data CedilleTypes.PosTerm (CedilleTypes.PosTerm) #-}
{-# COMPILE GHC ex-is-mu = data CedilleTypes.IsMu (CedilleTypes.IsMu | CedilleTypes.IsMu') #-}
{-# COMPILE GHC ex-tm = data CedilleTypes.Term (CedilleTypes.App | CedilleTypes.AppTp | CedilleTypes.Beta | CedilleTypes.Chi | CedilleTypes.Delta | CedilleTypes.Epsilon | CedilleTypes.Hole | CedilleTypes.IotaPair | CedilleTypes.IotaProj | CedilleTypes.Lam | CedilleTypes.Let | CedilleTypes.Open | CedilleTypes.Parens | CedilleTypes.Phi | CedilleTypes.Rho | CedilleTypes.Sigma | CedilleTypes.Theta | CedilleTypes.Mu | CedilleTypes.Var) #-}
{-# COMPILE GHC ex-kd = data CedilleTypes.Kind (CedilleTypes.KdAbs | CedilleTypes.KdArrow | CedilleTypes.KdHole | CedilleTypes.KdParens | CedilleTypes.KdStar | CedilleTypes.KdVar) #-}
