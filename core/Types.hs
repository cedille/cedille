module Types where

type Var = Int
type TpKd = PrimTpKd Term
type PureTpKd = PrimTpKd PureTerm
type Kind = PrimKind Term
type PureKind = PrimKind PureTerm
type Type = PrimType Term
type PureType = PrimType PureTerm
type Cmds = [Cmd]

data Cmd =
    TermCmd String Term
  | TypeCmd String Kind Type
  | ImportCmd String

data Term =
    TmVar Var
  | TmRef String
  | TmLam Type Term
  | TmLamE TpKd Term
  | TmAppTm Term Term
  | TmAppTmE Term Term
  | TmAppTp Term Type
  | TmIota Term Term Type
  | TmLetTm Term Term
  | TmLetTmE Term Term
  | TmLetTp Kind Type Term
  | IotaProj1 Term
  | IotaProj2 Term
  | Beta PureTerm PureTerm
  | Sigma Term
  | Delta PureType Term
  | Rho Term PureType Term
  | Phi Term Term PureTerm

data PureTerm =
    PureVar Var
  | PureRef String
  | PureLam PureTerm
  | PureApp PureTerm PureTerm

data PrimType tm =
    TpVar Var
  | TpRef String
  | TpLam (PrimTpKd tm) (PrimType tm)
  | TpAll (PrimTpKd tm) (PrimType tm)
  | TpPi (PrimType tm) (PrimType tm)
  | TpIota (PrimType tm) (PrimType tm)
  | TpEq PureTerm PureTerm
  | TpAppTp (PrimType tm) (PrimType tm)
  | TpAppTm (PrimType tm) tm

data PrimKind tm =
    Star
  | KdPi (PrimTpKd tm) (PrimKind tm)

data PrimTpKd tm =
    TpKdTp (PrimType tm)
  | TpKdKd (PrimKind tm)
