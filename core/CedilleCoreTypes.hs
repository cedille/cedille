module CedilleCoreTypes where

type Var = String
type Tk = PrimTk Term
type PureTk = PrimTk PureTerm
type Kind = PrimKind Term
type PureKind = PrimKind PureTerm
type Type = PrimType Term
type PureType = PrimType PureTerm

data Term =
    TmVar Var
  | TmLambda Var Type Term
  | TmLambdaE Var Tk Term
  | TmAppTm Term Term
  | TmAppTmE Term Term
  | TmAppTp Term Type
  | IotaPair Term Term Var Type
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
  | TpLambda Var (PrimTk tm) (PrimType tm)
  | TpAll Var (PrimTk tm) (PrimType tm)
  | TpPi Var (PrimType tm) (PrimType tm)
  | TpEq PureTerm PureTerm
  | TpAppTp (PrimType tm) (PrimType tm)
  | TpAppTm (PrimType tm) tm
  | Iota Var (PrimType tm) (PrimType tm)

data PrimKind tm =
    Star
  | KdPi Var (PrimTk tm) (PrimKind tm)

data PrimTk tm =
    Tkt (PrimType tm)
  | Tkk (PrimKind tm)

