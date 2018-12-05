module CedilleTypes where

import Prelude hiding(Num)
import CedilleLexer
import Data.Text(Text)

type Num = Text
type Fpth = Text
type Var = Text
type Bvar = Text
type Qvar = Text
type Qkvar = Text
type Kvar = Text
type PosInfo = Text

data Arg = TermArg MaybeErased Term | TypeArg Type
     deriving (Show,Eq)

type Args = [Arg]
     
type Opacity = Bool

data Cmd =
       DefKind PosInfo Kvar Params Kind PosInfo
     | DefTermOrType Opacity DefTermOrType PosInfo
     | DefDatatype  DefDatatype PosInfo               
     | ImportCmd Imprt
     deriving (Show,Eq)

type Cmds = [Cmd]

data Decl =
     Decl PosInfo PosInfo MaybeErased Bvar Tk PosInfo
     deriving (Show,Eq)

data DefDatatype =
     Datatype PosInfo PosInfo Var Params Kind Ctrs
     deriving (Show,Eq)

data DataCtr =
     Ctr PosInfo Var Type
     deriving (Show,Eq)

type Ctrs = [DataCtr]

data DefTermOrType =
       DefTerm PosInfo Var OptType Term
     | DefType PosInfo Var Kind Type
     deriving (Show,Eq)
     
type Imports = [Imprt]

data Imprt =
     Import PosInfo OptPublic PosInfo Fpth OptAs Args PosInfo
     deriving (Show,Eq)

data Kind =
       KndArrow Kind Kind
     | KndParens PosInfo Kind PosInfo
     | KndPi PosInfo PosInfo Bvar Tk Kind
     | KndTpArrow Type Kind
     | KndVar PosInfo Qkvar Args
     | Star PosInfo
     deriving (Show,Eq)

data LeftRight = Both | Left | Right
     deriving (Show,Eq)

data LiftingType =
       LiftArrow LiftingType LiftingType
     | LiftParens PosInfo LiftingType PosInfo
     | LiftPi PosInfo Bvar Type LiftingType
     | LiftStar PosInfo
     | LiftTpArrow Type LiftingType
     deriving (Show,Eq)

data Lterm = MkLterm MaybeErased Term
     deriving (Show,Eq)
type Lterms = [Lterm]

data OptType = SomeType Type | NoType
     deriving (Show,Eq)

type MaybeErased = Bool

type ForceErased = Bool

type MaybeMinus = Bool

data Nums =
     NumsStart Num | NumsNext Num Nums
     deriving (Show,Eq)

data OptAs = NoOptAs | SomeOptAs PosInfo Var
     deriving (Show,Eq)

data OptClass = NoClass | SomeClass Tk
     deriving (Show,Eq)

data OptGuide = NoGuide | Guide PosInfo Bvar Type
     deriving (Show,Eq)

data OptNums = NoNums | SomeNums Nums
     deriving (Show,Eq)

type RhoHnf = Bool

type OptPublic = Bool

data OptTerm = NoTerm | SomeTerm Term PosInfo
     deriving (Show,Eq)

type Params = [Decl]

data Start =
     File Imports PosInfo PosInfo Qvar Params Cmds PosInfo
     deriving (Show,Eq)
     
data Term =
       App Term MaybeErased Term
     | AppTp Term Type
     | Beta PosInfo OptTerm OptTerm
     | Chi PosInfo OptType Term
     | Delta PosInfo OptType Term
     | Epsilon PosInfo LeftRight MaybeMinus Term
     | Hole PosInfo
     | IotaPair PosInfo Term Term OptGuide PosInfo
     | IotaProj Term Num PosInfo
     | Lam PosInfo MaybeErased PosInfo Bvar OptClass Term
     | Let PosInfo ForceErased DefTermOrType Term
     | Open PosInfo Qvar Term
     | Parens PosInfo Term PosInfo
     | Phi PosInfo Term Term Term PosInfo
     | Rho PosInfo RhoHnf OptNums Term OptGuide Term
     | Sigma PosInfo Term
     | Theta PosInfo Theta Term Lterms
     | Mu  PosInfo PosInfo Bvar Term OptType PosInfo Cases PosInfo
     | Mu' PosInfo              Term OptType PosInfo Cases PosInfo     
     | Var PosInfo Qvar
     deriving (Show,Eq)

data Case = MkCase PosInfo Var CaseArgs Term
     deriving (Show,Eq)

type Cases = [Case]

data CaseArg =
    CaseTermArg PosInfo MaybeErased Bvar
  | CaseTypeArg PosInfo Bvar
  deriving (Show,Eq)
type CaseArgs = [CaseArg]

data Theta =
     Abstract | AbstractEq | AbstractVars Vars
     deriving (Show,Eq)

data Tk = Tkk Kind | Tkt Type
     deriving (Show,Eq)

data Type =
       Abs PosInfo MaybeErased PosInfo Bvar Tk Type
     | Iota PosInfo PosInfo Bvar Type Type
     | Lft PosInfo PosInfo Var Term LiftingType
     | NoSpans Type PosInfo
     | TpLet PosInfo DefTermOrType Type
     | TpApp Type Type
     | TpAppt Type Term
     | TpArrow Type MaybeErased Type
     | TpEq PosInfo Term Term PosInfo
     | TpHole PosInfo
     | TpLambda PosInfo PosInfo Bvar Tk Type
     | TpParens PosInfo Type PosInfo
     | TpVar PosInfo Qvar
     deriving (Show,Eq)

data Vars =
       VarsNext Var Vars
     | VarsStart Var
     deriving (Show,Eq)
