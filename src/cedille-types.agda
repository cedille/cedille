----------------------------------------------------------------------------------
-- Types for parse trees
----------------------------------------------------------------------------------

module cedille-types where

open import lib
-- open import parse-tree

posinfo = string
alpha = string
alpha-bar-3 = string
alpha-range-1 = string
alpha-range-2 = string
bvar = string
bvar-bar-13 = string
fpth = string
fpth-bar-15 = string
fpth-bar-16 = string
fpth-bar-17 = string
fpth-plus-14 = string
fpth-star-18 = string
kvar = string
kvar-bar-19 = string
kvar-star-20 = string
num = string
num-plus-5 = string
numone = string
numone-range-4 = string
numpunct = string
numpunct-bar-10 = string
numpunct-bar-6 = string
numpunct-bar-7 = string
numpunct-bar-8 = string
numpunct-bar-9 = string
qkvar = string
qvar = string
var = string
var-bar-11 = string
var-star-12 = string

{-# FOREIGN GHC import qualified CedilleTypes #-}

data arg : Set
{-# COMPILE GHC arg = type CedilleTypes.Arg #-}
data args : Set
{-# COMPILE GHC args = type CedilleTypes.Args #-}
data opacity : Set
{-# COMPILE GHC opacity = type CedilleTypes.Opacity #-}
data cmd : Set
{-# COMPILE GHC cmd = type CedilleTypes.Cmd #-}
data cmds : Set
{-# COMPILE GHC cmds = type CedilleTypes.Cmds #-}
data decl : Set
{-# COMPILE GHC decl = type CedilleTypes.Decl #-}
data defDatatype : Set
{-# COMPILE GHC defDatatype = type CedilleTypes.DefDatatype #-}
data dataConst : Set
{-# COMPILE GHC dataConst = type CedilleTypes.DataConst #-}
data dataConsts : Set
{-# COMPILE GHC dataConsts = type CedilleTypes.DataConsts #-}
data defTermOrType : Set
{-# COMPILE GHC defTermOrType = type CedilleTypes.DefTermOrType #-}
data imports : Set
{-# COMPILE GHC imports = type CedilleTypes.Imports #-}
data imprt : Set
{-# COMPILE GHC imprt = type CedilleTypes.Imprt #-}
data kind : Set
{-# COMPILE GHC kind = type CedilleTypes.Kind #-}
data leftRight : Set
{-# COMPILE GHC leftRight = type CedilleTypes.LeftRight #-}
data liftingType : Set
{-# COMPILE GHC liftingType = type CedilleTypes.LiftingType #-}
data lterms : Set
{-# COMPILE GHC lterms = type CedilleTypes.Lterms #-}
data optType : Set
{-# COMPILE GHC optType = type CedilleTypes.OptType #-}
data maybeErased : Set
{-# COMPILE GHC maybeErased = type CedilleTypes.MaybeErased #-}
data maybeMinus : Set
{-# COMPILE GHC maybeMinus = type CedilleTypes.MaybeMinus #-}
data nums : Set
{-# COMPILE GHC nums = type CedilleTypes.Nums #-}
data optAs : Set
{-# COMPILE GHC optAs = type CedilleTypes.OptAs #-}
data optClass : Set
{-# COMPILE GHC optClass = type CedilleTypes.OptClass #-}
data optGuide : Set
{-# COMPILE GHC optGuide = type CedilleTypes.OptGuide #-}
data optPlus : Set
{-# COMPILE GHC optPlus = type CedilleTypes.OptPlus #-}
data optNums : Set
{-# COMPILE GHC optNums = type CedilleTypes.OptNums #-}
data optPublic : Set
{-# COMPILE GHC optPublic = type CedilleTypes.OptPublic #-}
data optTerm : Set
{-# COMPILE GHC optTerm = type CedilleTypes.OptTerm #-}
data params : Set
{-# COMPILE GHC params = type CedilleTypes.Params #-}
data start : Set
{-# COMPILE GHC start = type CedilleTypes.Start #-}
data term : Set
{-# COMPILE GHC term = type CedilleTypes.Term  #-}
data theta : Set
{-# COMPILE GHC theta = type CedilleTypes.Theta  #-}
data tk : Set
{-# COMPILE GHC tk = type CedilleTypes.Tk  #-}
data type : Set
{-# COMPILE GHC type = type CedilleTypes.Type  #-}
data vars : Set
{-# COMPILE GHC vars = type CedilleTypes.Vars  #-}
data cases : Set
{-# COMPILE GHC cases = type CedilleTypes.Cases  #-}
data varargs : Set
{-# COMPILE GHC varargs = type CedilleTypes.Varargs  #-}

data arg where 
  TermArg : maybeErased → term → arg
  TypeArg : type → arg
{-# COMPILE GHC arg = data CedilleTypes.Arg (CedilleTypes.TermArg | CedilleTypes.TypeArg) #-}

data args where 
  ArgsCons : arg → args → args
  ArgsNil : args
{-# COMPILE GHC args = data CedilleTypes.Args (CedilleTypes.ArgsCons | CedilleTypes.ArgsNil) #-}

data opacity where 
  OpacOpaque : opacity
  OpacTrans : opacity
{-# COMPILE GHC opacity = data CedilleTypes.Opacity (CedilleTypes.OpacOpaque | CedilleTypes.OpacTrans) #-}

data cmd where 
  DefKind : posinfo → kvar → params → kind → posinfo → cmd
  DefTermOrType : opacity → defTermOrType → posinfo → cmd
  DefDatatype   : defDatatype   → posinfo → cmd    
  ImportCmd : imprt → cmd
{-# COMPILE GHC cmd = data CedilleTypes.Cmd (CedilleTypes.DefKind | CedilleTypes.DefTermOrType | CedilleTypes.DefDatatype |CedilleTypes.ImportCmd) #-}

data cmds where 
  CmdsNext : cmd → cmds → cmds
  CmdsStart : cmds
{-# COMPILE GHC cmds = data CedilleTypes.Cmds (CedilleTypes.CmdsNext | CedilleTypes.CmdsStart) #-}

data decl where 
  Decl : posinfo → posinfo → maybeErased → bvar → tk → posinfo → decl
{-# COMPILE GHC decl = data CedilleTypes.Decl (CedilleTypes.Decl) #-}

data defDatatype where 
  Datatype : posinfo → posinfo → var → params → kind → dataConsts → defDatatype
{-# COMPILE GHC defDatatype = data CedilleTypes.DefDatatype (CedilleTypes.Datatype) #-}

data dataConst where
  DataConst : posinfo → var → type → dataConst
{-# COMPILE GHC dataConst = data CedilleTypes.DataConst (CedilleTypes.DataConst) #-}

data dataConsts where
  DataNull : dataConsts
  DataCons : dataConst → dataConsts → dataConsts
{-# COMPILE GHC dataConsts = data CedilleTypes.DataConsts (CedilleTypes.DataNull | CedilleTypes.DataCons) #-}

data defTermOrType where 
  DefTerm : posinfo → var → optType → term → defTermOrType
  DefType : posinfo → var → kind → type → defTermOrType
{-# COMPILE GHC defTermOrType = data CedilleTypes.DefTermOrType (CedilleTypes.DefTerm | CedilleTypes.DefType) #-}

data imports where 
  ImportsNext : imprt → imports → imports
  ImportsStart : imports
{-# COMPILE GHC imports = data CedilleTypes.Imports (CedilleTypes.ImportsNext | CedilleTypes.ImportsStart) #-}

data imprt where 
  Import : posinfo → optPublic → posinfo → fpth → optAs → args → posinfo → imprt
{-# COMPILE GHC imprt = data CedilleTypes.Imprt (CedilleTypes.Import) #-}

data kind where 
  KndArrow : kind → kind → kind
  KndParens : posinfo → kind → posinfo → kind
  KndPi : posinfo → posinfo → bvar → tk → kind → kind
  KndTpArrow : type → kind → kind
  KndVar : posinfo → qkvar → args → kind
  Star : posinfo → kind
{-# COMPILE GHC kind = data CedilleTypes.Kind (CedilleTypes.KndArrow | CedilleTypes.KndParens | CedilleTypes.KndPi | CedilleTypes.KndTpArrow | CedilleTypes.KndVar | CedilleTypes.Star) #-}  

data leftRight where 
  Both : leftRight
  Left : leftRight
  Right : leftRight
{-# COMPILE GHC leftRight = data CedilleTypes.LeftRight (CedilleTypes.Both | CedilleTypes.Left | CedilleTypes.Right) #-}

data liftingType where 
  LiftArrow : liftingType → liftingType → liftingType
  LiftParens : posinfo → liftingType → posinfo → liftingType
  LiftPi : posinfo → bvar → type → liftingType → liftingType
  LiftStar : posinfo → liftingType
  LiftTpArrow : type → liftingType → liftingType
{-# COMPILE GHC liftingType = data CedilleTypes.LiftingType (CedilleTypes.LiftArrow | CedilleTypes.LiftParens | CedilleTypes.LiftPi | CedilleTypes.LiftStar | CedilleTypes.LiftTpArrow) #-}

data lterms where 
  LtermsCons : maybeErased → term → lterms → lterms
  LtermsNil : posinfo → lterms
{-# COMPILE GHC lterms = data CedilleTypes.Lterms (CedilleTypes.LtermsCons | CedilleTypes.LtermsNil) #-}

data optType where 
  SomeType : type → optType
  NoType : optType
{-# COMPILE GHC optType = data CedilleTypes.OptType (CedilleTypes.SomeType | CedilleTypes.NoType) #-}

data maybeErased where 
  Erased : maybeErased
  NotErased : maybeErased
{-# COMPILE GHC maybeErased = data CedilleTypes.MaybeErased (CedilleTypes.Erased | CedilleTypes.NotErased) #-}

data maybeMinus where 
  EpsHanf : maybeMinus
  EpsHnf : maybeMinus
{-# COMPILE GHC maybeMinus = data CedilleTypes.MaybeMinus (CedilleTypes.EpsHanf | CedilleTypes.EpsHnf) #-}

data nums where
  NumsStart : num → nums
  NumsNext : num → nums → nums
{-# COMPILE GHC nums = data CedilleTypes.Nums (CedilleTypes.NumsStart | CedilleTypes.NumsNext) #-}

data optAs where 
  NoOptAs : optAs
  SomeOptAs : posinfo → var → optAs
{-# COMPILE GHC optAs = data CedilleTypes.OptAs (CedilleTypes.NoOptAs | CedilleTypes.SomeOptAs) #-}

data optPublic where
  NotPublic : optPublic
  IsPublic : optPublic
{-# COMPILE GHC optPublic = data CedilleTypes.OptPublic (CedilleTypes.NotPublic | CedilleTypes.IsPublic) #-}

data optClass where 
  NoClass : optClass
  SomeClass : tk → optClass
{-# COMPILE GHC optClass = data CedilleTypes.OptClass (CedilleTypes.NoClass | CedilleTypes.SomeClass) #-}

data optGuide where 
  NoGuide : optGuide
  Guide : posinfo → var → type → optGuide
{-# COMPILE GHC optGuide = data CedilleTypes.OptGuide (CedilleTypes.NoGuide | CedilleTypes.Guide) #-}

data optPlus where 
  RhoPlain : optPlus
  RhoPlus : optPlus
{-# COMPILE GHC optPlus = data CedilleTypes.OptPlus (CedilleTypes.RhoPlain | CedilleTypes.RhoPlus) #-}

data optNums where 
  NoNums : optNums
  SomeNums : nums → optNums
{-# COMPILE GHC optNums = data CedilleTypes.OptNums (CedilleTypes.NoNums | CedilleTypes.SomeNums) #-}

data optTerm where 
  NoTerm : optTerm
  SomeTerm : term → posinfo → optTerm
{-# COMPILE GHC optTerm = data CedilleTypes.OptTerm (CedilleTypes.NoTerm | CedilleTypes.SomeTerm) #-}  

data params where 
  ParamsCons : decl → params → params
  ParamsNil : params
{-# COMPILE GHC params = data CedilleTypes.Params (CedilleTypes.ParamsCons | CedilleTypes.ParamsNil) #-}

data start where 
  File : posinfo → imports → posinfo → posinfo → qvar → params → cmds → posinfo → start
{-# COMPILE GHC start = data CedilleTypes.Start (CedilleTypes.File) #-}  

data term where 
  App : term → maybeErased → term → term
  AppTp : term → type → term
  Beta : posinfo → optTerm → optTerm → term
  Chi : posinfo → optType → term → term
  Delta : posinfo → optType → term → term
  Epsilon : posinfo → leftRight → maybeMinus → term → term
  Hole : posinfo → term
  IotaPair : posinfo → term → term → optGuide → posinfo → term
  IotaProj : term → num → posinfo → term
  Lam : posinfo → maybeErased → posinfo → bvar → optClass → term → term
  Let : posinfo → defTermOrType → term → term
  Open : posinfo → var → term → term
  Parens : posinfo → term → posinfo → term
  Phi : posinfo → term → term → term → posinfo → term  
  Rho : posinfo → optPlus → optNums → term → optGuide → term → term
  Sigma : posinfo → term → term
  Theta : posinfo → theta → term → lterms → term
  Mu  : posinfo → bvar → term → optType → cases → posinfo → term
  Mu' : posinfo → term → optType → cases → posinfo → term
  Var : posinfo → qvar → term
{-# COMPILE GHC term = data CedilleTypes.Term (CedilleTypes.App | CedilleTypes.AppTp | CedilleTypes.Beta | CedilleTypes.Chi | CedilleTypes.Delta | CedilleTypes.Epsilon | CedilleTypes.Hole | CedilleTypes.IotaPair | CedilleTypes.IotaProj | CedilleTypes.Lam | CedilleTypes.Let | CedilleTypes.Parens | CedilleTypes.Phi | CedilleTypes.Rho | CedilleTypes.Sigma | CedilleTypes.Theta | CedilleTypes.Mu | CedilleTypes.Mu' | CedilleTypes.Var) #-}

data cases where
  NoCase : cases
  SomeCase : var → varargs → term → cases → cases
{-# COMPILE GHC cases = data CedilleTypes.Cases (CedilleTypes.NoCase | CedilleTypes.SomeCase) #-}

data varargs where
  NoVarargs : varargs
  NormalVararg : bvar → varargs → varargs 
  ErasedVararg : bvar → varargs → varargs 
  TypeVararg   : bvar → varargs → varargs 
{-# COMPILE GHC varargs = data CedilleTypes.Varargs (CedilleTypes.NoVarargs | CedilleTypes.NormalVararg | CedilleTypes.ErasedVararg | CedilleTypes.TypeVararg ) #-}  
  
data theta where 
  Abstract : theta
  AbstractEq : theta
  AbstractVars : vars → theta
{-# COMPILE GHC theta = data CedilleTypes.Theta (CedilleTypes.Abstract | CedilleTypes.AbstractEq | CedilleTypes.AbstractVars) #-}      

data tk where 
  Tkk : kind → tk
  Tkt : type → tk
{-# COMPILE GHC tk = data CedilleTypes.Tk (CedilleTypes.Tkk | CedilleTypes.Tkt) #-}        

data type where 
  Abs : posinfo → maybeErased → posinfo → bvar → tk → type → type
  Iota : posinfo → posinfo → bvar → type → type → type
  Lft : posinfo → posinfo → var → term → liftingType → type
  NoSpans : type → posinfo → type
  TpLet : posinfo → defTermOrType → type → type
  TpApp : type → type → type
  TpAppt : type → term → type
  TpArrow : type → maybeErased → type → type
  TpEq : posinfo → term → term → posinfo → type
  TpHole : posinfo → type
  TpLambda : posinfo → posinfo → bvar → tk → type → type
  TpParens : posinfo → type → posinfo → type
  TpVar : posinfo → qvar → type
{-# COMPILE GHC type = data CedilleTypes.Type (CedilleTypes.Abs | CedilleTypes.Iota | CedilleTypes.Lft | CedilleTypes.NoSpans | CedilleTypes.TpLet | CedilleTypes.TpApp | CedilleTypes.TpAppt | CedilleTypes.TpArrow | CedilleTypes.TpEq | CedilleTypes.TpHole | CedilleTypes.TpLambda | CedilleTypes.TpParens | CedilleTypes.TpVar) #-}

data vars where 
  VarsNext : var → vars → vars
  VarsStart : var → vars
{-# COMPILE GHC vars = data CedilleTypes.Vars (CedilleTypes.VarsNext | CedilleTypes.VarsStart) #-}

pattern Pi = NotErased
pattern All = Erased

-- embedded types:
aterm = term
atype = type
lliftingType = liftingType
lterm = term
ltype = type
pterm = term
