module Types where

data Term =
    TmVar Int
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
  | TmProj1 Term
  | TmProj2 Term
  | TmBeta PrTerm PrTerm
  | TmSigma Term
  | TmDelta PrType Term
  | TmRho Term PrType Term
  | TmPhi Term Term PrTerm

data PrTerm =
    PrVar Int
  | PrRef String
  | PrLam PrTerm
  | PrApp PrTerm PrTerm

data BaseType tm =
    TpVar Int
  | TpRef String
  | TpLam (BaseTpKd tm) (BaseType tm)
  | TpAll (BaseTpKd tm) (BaseType tm)
  | TpPi (BaseType tm) (BaseType tm)
  | TpIota (BaseType tm) (BaseType tm)
  | TpEq PrTerm PrTerm
  | TpAppTp (BaseType tm) (BaseType tm)
  | TpAppTm (BaseType tm) tm

data BaseKind tm =
    KdStar
  | KdPi (BaseTpKd tm) (BaseKind tm)

type Type = BaseType Term
type Kind = BaseKind Term
type TpKd = BaseTpKd Term
type TmTp = BaseTmTp Term
type PrType = BaseType PrTerm
type PrKind = BaseKind PrTerm
type PrTpKd = BaseTpKd PrTerm
type PrTmTp = BaseTmTp PrTerm

type BaseTpKd tm = Either (BaseType tm) (BaseKind tm)
type BaseTmTp tm = Either tm (BaseType tm)

type Cmds = [Cmd]

data Cmd =
    TermCmd String Term
  | TypeCmd String Kind Type
  | ImportCmd String
