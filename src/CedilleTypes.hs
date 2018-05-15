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

data Arg = TermArg Term | TypeArg Type
     deriving (Show,Eq)

data Args = ArgsCons Arg Args | ArgsNil
     deriving (Show,Eq)
     
data ArrowType = ErasedArrow | UnerasedArrow
     deriving (Show,Eq)
     
data Binder = All | Pi
     deriving (Show,Eq)
     
data Cmd =
       DefKind PosInfo Kvar Params Kind PosInfo
     | DefTermOrType DefTermOrType PosInfo
     | ImportCmd Imprt
     deriving (Show,Eq)

data Cmds =
        CmdsNext Cmd Cmds
      | CmdsStart 
      deriving (Show,Eq)

data Decl =
     Decl PosInfo PosInfo Bvar Tk PosInfo
     deriving (Show,Eq)

data DefTermOrType =
       DefTerm PosInfo Var MaybeCheckType Term
     | DefType PosInfo Var Kind Type
     deriving (Show,Eq)
     
data Imports =
       ImportsNext Imprt Imports
     | ImportsStart
     deriving (Show,Eq)

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

data Lam = ErasedLambda | KeptLambda
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

data Lterms =
       LtermsCons MaybeErased Term Lterms
     | LtermsNil PosInfo
     deriving (Show,Eq)

data MaybeAtype = Atype Type | NoAtype 
     deriving (Show,Eq)

data MaybeCheckType =
     NoCheckType | Type Type
     deriving (Show,Eq)

data MaybeErased =
     Erased | NotErased
     deriving (Show,Eq)

data MaybeMinus =
     EpsHanf | EpsHnf
     deriving (Show,Eq)

data Nums =
     NumsStart Num | NumsNext Num Nums
     deriving (Show,Eq)

data OptAs =
     NoOptAs | SomeOptAs PosInfo Var
     deriving (Show,Eq)

data OptClass =
     NoClass | SomeClass Tk
     deriving (Show,Eq)

data OptGuide =
     NoGuide | Guide PosInfo Bvar Type
     deriving (Show,Eq)

data OptNums =
     NoNums | SomeNums Nums
     deriving (Show,Eq)

data OptPlus =
     RhoPlain | RhoPlus
     deriving (Show,Eq)

data OptPublic =
     NotPublic | IsPublic
     deriving (Show,Eq)

data OptTerm =
     NoTerm | SomeTerm Term PosInfo
     deriving (Show,Eq)

data Params =
       ParamsCons Decl Params
     | ParamsNil
     deriving (Show,Eq)

data Start =
     File PosInfo Imports PosInfo PosInfo Qvar Params Cmds PosInfo
     deriving (Show,Eq)
     
data Term =
       App Term MaybeErased Term
     | AppTp Term Type
     | Beta PosInfo OptTerm OptTerm
     | Chi PosInfo MaybeAtype Term
     | Delta PosInfo MaybeAtype Term
     | Epsilon PosInfo LeftRight MaybeMinus Term
     | Hole PosInfo
     | IotaPair PosInfo Term Term OptGuide PosInfo
     | IotaProj Term Num PosInfo
     | Lam PosInfo Lam PosInfo Bvar OptClass Term
     | Let PosInfo DefTermOrType Term
     | Parens PosInfo Term PosInfo
     | Phi PosInfo Term Term Term PosInfo
     | Rho PosInfo OptPlus OptNums Term OptGuide Term
     | Sigma PosInfo Term
     | Theta PosInfo Theta Term Lterms
     | Var PosInfo Qvar
     deriving (Show,Eq)
     
data Theta =
     Abstract | AbstractEq | AbstractVars Vars
     deriving (Show,Eq)

data Tk = Tkk Kind | Tkt Type
     deriving (Show,Eq)

data Type =
       Abs PosInfo Binder PosInfo Bvar Tk Type
     | Iota PosInfo PosInfo Bvar Type Type
     | Lft PosInfo PosInfo Var Term LiftingType
     | NoSpans Type PosInfo
     | TpApp Type Type
     | TpAppt Type Term
     | TpArrow Type ArrowType Type
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
