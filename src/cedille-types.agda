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
args : Set
opacity : Set
data cmd : Set
cmds : Set
data decl : Set
data defDatatype : Set
data ctr : Set
ctrs : Set
data defTermOrType : Set
imports : Set
data imprt : Set
data kind : Set
data leftRight : Set
data liftingType : Set
data lterm : Set
lterms : Set
data optType : Set
maybeErased : Set
maybeMinus : Set
data nums : Set
data optAs : Set
data optClass : Set
data optGuide : Set
rhoHnf : Set
data optNums : Set
optPublic : Set
data optTerm : Set
params : Set
data start : Set
data term : Set
data theta : Set
data tk : Set
data type : Set
data vars : Set
cases : Set
data case : Set
caseArgs : Set
data caseArg : Set

{-# COMPILE GHC arg = type CedilleTypes.Arg #-}
{-# COMPILE GHC args = type CedilleTypes.Args #-}
{-# COMPILE GHC opacity = type CedilleTypes.Opacity #-}
{-# COMPILE GHC cmd = type CedilleTypes.Cmd #-}
{-# COMPILE GHC cmds = type CedilleTypes.Cmds #-}
{-# COMPILE GHC decl = type CedilleTypes.Decl #-}
{-# COMPILE GHC defDatatype = type CedilleTypes.DefDatatype #-}
{-# COMPILE GHC ctr = type CedilleTypes.DataCtr #-}
{-# COMPILE GHC ctrs = type CedilleTypes.Ctrs #-}
{-# COMPILE GHC defTermOrType = type CedilleTypes.DefTermOrType #-}
{-# COMPILE GHC imports = type CedilleTypes.Imports #-}
{-# COMPILE GHC imprt = type CedilleTypes.Imprt #-}
{-# COMPILE GHC kind = type CedilleTypes.Kind #-}
{-# COMPILE GHC leftRight = type CedilleTypes.LeftRight #-}
{-# COMPILE GHC liftingType = type CedilleTypes.LiftingType #-}
{-# COMPILE GHC lterm = type CedilleTypes.Lterm #-}
{-# COMPILE GHC lterms = type CedilleTypes.Lterms #-}
{-# COMPILE GHC optType = type CedilleTypes.OptType #-}
{-# COMPILE GHC maybeErased = type CedilleTypes.MaybeErased #-}
{-# COMPILE GHC maybeMinus = type CedilleTypes.MaybeMinus #-}
{-# COMPILE GHC nums = type CedilleTypes.Nums #-}
{-# COMPILE GHC optAs = type CedilleTypes.OptAs #-}
{-# COMPILE GHC optClass = type CedilleTypes.OptClass #-}
{-# COMPILE GHC optGuide = type CedilleTypes.OptGuide #-}
{-# COMPILE GHC rhoHnf = type CedilleTypes.RhoHnf #-}
{-# COMPILE GHC optNums = type CedilleTypes.OptNums #-}
{-# COMPILE GHC optPublic = type CedilleTypes.OptPublic #-}
{-# COMPILE GHC optTerm = type CedilleTypes.OptTerm #-}
{-# COMPILE GHC params = type CedilleTypes.Params #-}
{-# COMPILE GHC start = type CedilleTypes.Start #-}
{-# COMPILE GHC term = type CedilleTypes.Term  #-}
{-# COMPILE GHC theta = type CedilleTypes.Theta  #-}
{-# COMPILE GHC tk = type CedilleTypes.Tk  #-}
{-# COMPILE GHC type = type CedilleTypes.Type  #-}
{-# COMPILE GHC vars = type CedilleTypes.Vars  #-}
{-# COMPILE GHC cases = type CedilleTypes.Cases  #-}
{-# COMPILE GHC case = type CedilleTypes.Case #-}
{-# COMPILE GHC caseArgs = type CedilleTypes.CaseArgs  #-}
{-# COMPILE GHC caseArg = type CedilleTypes.CaseArg #-}

data arg where 
  TermArg : maybeErased → term → arg
  TypeArg : type → arg
{-# COMPILE GHC arg = data CedilleTypes.Arg (CedilleTypes.TermArg | CedilleTypes.TypeArg) #-}

args = 𝕃 arg

opacity = 𝔹

data cmd where 
  DefKind : posinfo → kvar → params → kind → posinfo → cmd
  DefTermOrType : opacity → defTermOrType → posinfo → cmd
  DefDatatype   : defDatatype   → posinfo → cmd    
  ImportCmd : imprt → cmd
{-# COMPILE GHC cmd = data CedilleTypes.Cmd (CedilleTypes.DefKind | CedilleTypes.DefTermOrType | CedilleTypes.DefDatatype |CedilleTypes.ImportCmd) #-}

cmds = 𝕃 cmd

data decl where 
  Decl : posinfo → posinfo → maybeErased → bvar → tk → posinfo → decl
{-# COMPILE GHC decl = data CedilleTypes.Decl (CedilleTypes.Decl) #-}

data defDatatype where 
  Datatype : posinfo → posinfo → var → params → kind → ctrs → defDatatype
{-# COMPILE GHC defDatatype = data CedilleTypes.DefDatatype (CedilleTypes.Datatype) #-}

data ctr where
  Ctr : posinfo → var → type → ctr
{-# COMPILE GHC ctr = data CedilleTypes.DataCtr (CedilleTypes.Ctr) #-}

ctrs = 𝕃 ctr

data defTermOrType where 
  DefTerm : posinfo → var → optType → term → defTermOrType
  DefType : posinfo → var → kind → type → defTermOrType
{-# COMPILE GHC defTermOrType = data CedilleTypes.DefTermOrType (CedilleTypes.DefTerm | CedilleTypes.DefType) #-}

imports = 𝕃 imprt

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

data lterm where
  Lterm : maybeErased → term → lterm
{-# COMPILE GHC lterm = data CedilleTypes.Lterm (CedilleTypes.MkLterm) #-}

lterms = 𝕃 lterm

data optType where
  SomeType : type → optType
  NoType : optType
{-# COMPILE GHC optType = data CedilleTypes.OptType (CedilleTypes.SomeType | CedilleTypes.NoType) #-}

maybeErased = 𝔹

maybeMinus = 𝔹

data nums where
  NumsStart : num → nums
  NumsNext : num → nums → nums
{-# COMPILE GHC nums = data CedilleTypes.Nums (CedilleTypes.NumsStart | CedilleTypes.NumsNext) #-}

data optAs where
  NoOptAs : optAs
  SomeOptAs : posinfo → var → optAs
{-# COMPILE GHC optAs = data CedilleTypes.OptAs (CedilleTypes.NoOptAs | CedilleTypes.SomeOptAs) #-}

optPublic = 𝔹

data optClass where
  NoClass : optClass
  SomeClass : tk → optClass
{-# COMPILE GHC optClass = data CedilleTypes.OptClass (CedilleTypes.NoClass | CedilleTypes.SomeClass) #-}

data optGuide where 
  NoGuide : optGuide
  Guide : posinfo → var → type → optGuide
{-# COMPILE GHC optGuide = data CedilleTypes.OptGuide (CedilleTypes.NoGuide | CedilleTypes.Guide) #-}

rhoHnf = 𝔹

data optNums where 
  NoNums : optNums
  SomeNums : nums → optNums
{-# COMPILE GHC optNums = data CedilleTypes.OptNums (CedilleTypes.NoNums | CedilleTypes.SomeNums) #-}

data optTerm where
  NoTerm : optTerm
  SomeTerm : term → posinfo → optTerm
{-# COMPILE GHC optTerm = data CedilleTypes.OptTerm (CedilleTypes.NoTerm | CedilleTypes.SomeTerm) #-}

params = 𝕃 decl

data start where 
  File : imports → posinfo → posinfo → qvar → params → cmds → posinfo → start
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
  Rho : posinfo → rhoHnf → optNums → term → optGuide → term → term
  Sigma : posinfo → term → term
  Theta : posinfo → theta → term → lterms → term
  Mu  : posinfo → bvar → term → optType → posinfo → cases → posinfo → term
  Mu' : posinfo → term → optType → posinfo → cases → posinfo → term
  Var : posinfo → qvar → term
{-# COMPILE GHC term = data CedilleTypes.Term (CedilleTypes.App | CedilleTypes.AppTp | CedilleTypes.Beta | CedilleTypes.Chi | CedilleTypes.Delta | CedilleTypes.Epsilon | CedilleTypes.Hole | CedilleTypes.IotaPair | CedilleTypes.IotaProj | CedilleTypes.Lam | CedilleTypes.Let | CedilleTypes.Open | CedilleTypes.Parens | CedilleTypes.Phi | CedilleTypes.Rho | CedilleTypes.Sigma | CedilleTypes.Theta | CedilleTypes.Mu | CedilleTypes.Mu' | CedilleTypes.Var) #-}

data case where
  Case : posinfo → var → caseArgs → term → case
{-# COMPILE GHC case = data CedilleTypes.Case (CedilleTypes.MkCase) #-}

cases = 𝕃 case

data caseArg where
  CaseTermArg : posinfo → maybeErased → var → caseArg
  CaseTypeArg : posinfo → var → caseArg
{-# COMPILE GHC caseArg = data CedilleTypes.CaseArg (CedilleTypes.CaseTermArg | CedilleTypes.CaseTypeArg) #-}

caseArgs = 𝕃 caseArg
  
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

pattern Erased = tt
pattern NotErased = ff
pattern Pi = NotErased
pattern All = Erased
pattern OpacTrans = tt
pattern OpacOpaque = ff
pattern IsPublic = tt
pattern NotPublic = ff
pattern EpsHnf = ff
pattern EpsHanf = tt
pattern RhoPlain = ff
pattern RhoPlus = tt

-- embedded types:
-- aterm = term
-- atype = type
-- lliftingType = liftingType
-- lterm = term
-- ltype = type
-- pterm = term
