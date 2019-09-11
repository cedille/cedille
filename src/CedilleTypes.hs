module CedilleTypes where

import Prelude hiding(Num)
import CedilleLexer
import Data.Text(Text)

type Num = Text
type Fpth = Text
type Var = Text
type PosInfo = Text
type MaybeErased = Bool
type MaybeMinus = Bool
type LeftRight = Maybe Bool
type Opacity = Bool
type RhoHnf = Bool
type OptPublic = Bool
type Imports = [Imprt]
type Params = [Param]
type Cmds = [Cmd]
type Ctrs = [Ctr]
type Args = [Arg]
type Cases = [Case]

data Param = Param PosInfo MaybeErased PosInfo Var TpKd PosInfo deriving Show

data File = Module Imports PosInfo PosInfo Var Params Cmds PosInfo deriving Show

data Cmd =
    CmdKind PosInfo Var Params Kind PosInfo
  | CmdDef Opacity Def PosInfo
  | CmdData (DefDatatype , [SubsidiaryDefDatatype]) PosInfo
  | CmdImport Imprt
  deriving Show

data Ctr = Ctr PosInfo Var Type deriving Show

data DefDatatype = DefDatatype PosInfo PosInfo Var Params Kind Ctrs deriving Show

data SubsidiaryDefDatatype = SubsidiaryDefDatatype PosInfo PosInfo Var Ctrs deriving Show

data ImportAs = ImportAs PosInfo Var deriving Show
data Imprt = Import PosInfo OptPublic PosInfo Fpth (Maybe ImportAs) Args PosInfo deriving Show

data Arg = TermArg MaybeErased Term | TypeArg Type deriving Show

data CaseArgSym = CaseArgTm {- x -} | CaseArgEr {- -x -} | CaseArgTp {- ·x -} deriving Show

data Lterm = Lterm MaybeErased Term deriving Show

data Theta = Abstract | AbstractEq | AbstractVars [Var] deriving Show

data Def = DefTerm PosInfo Var (Maybe Type) Term | DefType PosInfo Var Kind Type deriving Show

data Guide = Guide PosInfo Var Type deriving Show

data Case = Case PosInfo Var [CaseArg] Term deriving Show

data CaseArg = CaseArg CaseArgSym PosInfo Var deriving Show

data TpKd = Tkt Type | Tkk Kind deriving Show

data Type =
    TpAbs PosInfo MaybeErased PosInfo Var TpKd Type
  | TpIota PosInfo PosInfo Var Type Type
--  | TpLft PosInfo PosInfo Var Term LiftingType
  | TpNoSpans Type PosInfo
  | TpLet PosInfo Def Type
  | TpApp Type Type
  | TpAppt Type Term
  | TpArrow Type MaybeErased Type
  | TpEq PosInfo Term Term PosInfo
  | TpHole PosInfo
  | TpLam PosInfo PosInfo Var TpKd Type
  | TpParens PosInfo Type PosInfo
  | TpVar PosInfo Var
  deriving Show

data PosTerm = PosTerm Term PosInfo deriving Show

data MotiveCases = MotiveCases (Maybe Type) PosInfo Cases PosInfo deriving Show

data Term =
    App Term MaybeErased Term
  | AppTp Term Type
  | Beta PosInfo (Maybe PosTerm) (Maybe PosTerm)
  | Chi PosInfo (Maybe Type) Term
  | Delta PosInfo (Maybe Type) Term
  | Epsilon PosInfo LeftRight MaybeMinus Term
  | Hole PosInfo
  | IotaPair PosInfo Term Term (Maybe Guide) PosInfo
  | IotaProj Term Num PosInfo
  | Lam PosInfo MaybeErased PosInfo Var (Maybe TpKd) Term
  | Let PosInfo MaybeErased Def Term
  | Open PosInfo Opacity PosInfo Var Term
  | Parens PosInfo Term PosInfo
  | Phi PosInfo Term Term Term PosInfo
  | Rho PosInfo RhoHnf (Maybe [Num]) Term (Maybe Guide) Term
  | Sigma PosInfo Term
  | Theta PosInfo Theta Term [Lterm]
  | Mu PosInfo PosInfo Var Term [MotiveCases] 
  | MuPrime PosInfo (Maybe Term) Term MotiveCases
  | Var PosInfo Var
  deriving Show

data Kind =
    KdAbs PosInfo PosInfo Var TpKd Kind
  | KdArrow TpKd Kind
  | KdHole PosInfo
  | KdParens PosInfo Kind PosInfo
  | KdStar PosInfo
  | KdVar PosInfo Var Args
  deriving Show
