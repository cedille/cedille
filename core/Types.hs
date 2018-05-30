module Types where

type Var = String
type TpKd = PrimTpKd Term
type PureTpKd = PrimTpKd PureTerm
type Kind = PrimKind Term
type PureKind = PrimKind PureTerm
type Type = PrimType Term
type PureType = PrimType PureTerm

data Cmds =
    CmdsStart
  | CmdsNext Cmd Cmds

data Cmd =
    TermCmd Var Term
  | TypeCmd Var Kind Type
  | ImportCmd String

data Term =
    TmVar Var
  | TmLambda Var Type Term
  | TmLambdaE Var TpKd Term
  | TmAppTm Term Term
  | TmAppTmE Term Term
  | TmAppTp Term Type
  | TmIota Term Term Var Type
  | IotaProj1 Term
  | IotaProj2 Term
  | Beta PureTerm PureTerm
  | Sigma Term
  | Delta PureType Term
  | Rho Term Var PureType Term
  | Phi Term Term PureTerm

data PureTerm =
    PureVar Var
  | PureLambda Var PureTerm
  | PureApp PureTerm PureTerm

data PrimType tm =
    TpVar Var
  | TpLambda Var (PrimTpKd tm) (PrimType tm)
  | TpAll Var (PrimTpKd tm) (PrimType tm)
  | TpPi Var (PrimType tm) (PrimType tm)
  | TpEq PureTerm PureTerm
  | TpAppTp (PrimType tm) (PrimType tm)
  | TpAppTm (PrimType tm) tm
  | TpIota Var (PrimType tm) (PrimType tm)

data PrimKind tm =
    Star
  | KdPi Var (PrimTpKd tm) (PrimKind tm)

data PrimTpKd tm =
    TpKdTp (PrimType tm)
  | TpKdKd (PrimKind tm)

