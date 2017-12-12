----------------------------------------------------------------------------------
-- Types for parse trees
----------------------------------------------------------------------------------

module cedille-types where

open import lib
open import parse-tree

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

mutual

  data arg : Set where 
    TermArg : term → arg
    TypeArg : type → arg

  data args : Set where 
    ArgsCons : arg → args → args
    ArgsNil : posinfo → args

  data arrowtype : Set where 
    ErasedArrow : arrowtype
    UnerasedArrow : arrowtype

  data binder : Set where 
    All : binder
    Pi : binder

  data cmd : Set where 
    DefKind : posinfo → kvar → params → kind → posinfo → cmd
    DefTermOrType : defTermOrType → posinfo → cmd
    ImportCmd : imprt → cmd

  data cmds : Set where 
    CmdsNext : cmd → cmds → cmds
    CmdsStart : cmds

  data decl : Set where 
    Decl : posinfo → posinfo → bvar → tk → posinfo → decl

  data defTermOrType : Set where 
    DefTerm : posinfo → var → maybeCheckType → term → defTermOrType
    DefType : posinfo → var → kind → type → defTermOrType

  data imports : Set where 
    ImportsNext : imprt → imports → imports
    ImportsStart : imports

  data imprt : Set where 
    Import : posinfo → fpth → optAs → args → posinfo → imprt

  data kind : Set where 
    KndArrow : kind → kind → kind
    KndParens : posinfo → kind → posinfo → kind
    KndPi : posinfo → posinfo → bvar → tk → kind → kind
    KndTpArrow : type → kind → kind
    KndVar : posinfo → qkvar → args → kind
    Star : posinfo → kind

  data lam : Set where 
    ErasedLambda : lam
    KeptLambda : lam

  data leftRight : Set where 
    Both : leftRight
    Left : leftRight
    Right : leftRight

  data liftingType : Set where 
    LiftArrow : liftingType → liftingType → liftingType
    LiftParens : posinfo → liftingType → posinfo → liftingType
    LiftPi : posinfo → bvar → type → liftingType → liftingType
    LiftStar : posinfo → liftingType
    LiftTpArrow : type → liftingType → liftingType

  data lterms : Set where 
    LtermsCons : maybeErased → term → lterms → lterms
    LtermsNil : posinfo → lterms

  data maybeAtype : Set where 
    Atype : type → maybeAtype
    NoAtype : maybeAtype

  data maybeCheckType : Set where 
    NoCheckType : maybeCheckType
    Type : type → maybeCheckType

  data maybeErased : Set where 
    Erased : maybeErased
    NotErased : maybeErased

  data maybeMinus : Set where 
    EpsHanf : maybeMinus
    EpsHnf : maybeMinus

  data optAs : Set where 
    NoOptAs : optAs
    SomeOptAs : var → optAs

  data optClass : Set where 
    NoClass : optClass
    SomeClass : tk → optClass

  data optTerm : Set where 
    NoTerm : optTerm
    SomeTerm : term → posinfo → optTerm

  data optType : Set where 
    NoType : optType
    SomeType : type → optType

  data params : Set where 
    ParamsCons : decl → params → params
    ParamsNil : params

  data rho : Set where 
    RhoPlain : rho
    RhoPlus : rho

  data start : Set where 
    File : posinfo → imports → qvar → params → cmds → posinfo → start

  data term : Set where 
    App : term → maybeErased → term → term
    AppTp : term → type → term
    Beta : posinfo → optTerm → term
    Chi : posinfo → maybeAtype → term → term
    Epsilon : posinfo → leftRight → maybeMinus → term → term
    Hole : posinfo → term
    IotaPair : posinfo → term → term → optTerm → posinfo → term
    IotaProj : term → num → posinfo → term
    Lam : posinfo → lam → posinfo → bvar → optClass → term → term
    Let : posinfo → defTermOrType → term → term
    Parens : posinfo → term → posinfo → term
    Rho : posinfo → rho → term → term → term
    Sigma : posinfo → term → term
    Theta : posinfo → theta → term → lterms → term
    Var : posinfo → qvar → term

  data theta : Set where 
    Abstract : theta
    AbstractEq : theta
    AbstractVars : vars → theta

  data tk : Set where 
    Tkk : kind → tk
    Tkt : type → tk

  data type : Set where 
    Abs : posinfo → binder → posinfo → bvar → tk → type → type
    Iota : posinfo → posinfo → bvar → optType → type → type
    Lft : posinfo → posinfo → var → term → liftingType → type
    NoSpans : type → posinfo → type
    TpApp : type → type → type
    TpAppt : type → term → type
    TpArrow : type → arrowtype → type → type
    TpEq : term → term → type
    TpHole : posinfo → type
    TpLambda : posinfo → posinfo → bvar → tk → type → type
    TpParens : posinfo → type → posinfo → type
    TpVar : posinfo → qvar → type

  data vars : Set where 
    VarsNext : var → vars → vars
    VarsStart : var → vars

-- embedded types:
aterm : Set
aterm = term
atype : Set
atype = type
lliftingType : Set
lliftingType = liftingType
lterm : Set
lterm = term
ltype : Set
ltype = type
pterm : Set
pterm = term

data ParseTreeT : Set where
  parsed-arg : arg → ParseTreeT
  parsed-args : args → ParseTreeT
  parsed-arrowtype : arrowtype → ParseTreeT
  parsed-binder : binder → ParseTreeT
  parsed-cmd : cmd → ParseTreeT
  parsed-cmds : cmds → ParseTreeT
  parsed-decl : decl → ParseTreeT
  parsed-defTermOrType : defTermOrType → ParseTreeT
  parsed-imports : imports → ParseTreeT
  parsed-imprt : imprt → ParseTreeT
  parsed-kind : kind → ParseTreeT
  parsed-lam : lam → ParseTreeT
  parsed-leftRight : leftRight → ParseTreeT
  parsed-liftingType : liftingType → ParseTreeT
  parsed-lterms : lterms → ParseTreeT
  parsed-maybeAtype : maybeAtype → ParseTreeT
  parsed-maybeCheckType : maybeCheckType → ParseTreeT
  parsed-maybeErased : maybeErased → ParseTreeT
  parsed-maybeMinus : maybeMinus → ParseTreeT
  parsed-optAs : optAs → ParseTreeT
  parsed-optClass : optClass → ParseTreeT
  parsed-optTerm : optTerm → ParseTreeT
  parsed-optType : optType → ParseTreeT
  parsed-params : params → ParseTreeT
  parsed-rho : rho → ParseTreeT
  parsed-start : start → ParseTreeT
  parsed-term : term → ParseTreeT
  parsed-theta : theta → ParseTreeT
  parsed-tk : tk → ParseTreeT
  parsed-type : type → ParseTreeT
  parsed-vars : vars → ParseTreeT
  parsed-aterm : term → ParseTreeT
  parsed-atype : type → ParseTreeT
  parsed-lliftingType : liftingType → ParseTreeT
  parsed-lterm : term → ParseTreeT
  parsed-ltype : type → ParseTreeT
  parsed-pterm : term → ParseTreeT
  parsed-posinfo : posinfo → ParseTreeT
  parsed-alpha : alpha → ParseTreeT
  parsed-alpha-bar-3 : alpha-bar-3 → ParseTreeT
  parsed-alpha-range-1 : alpha-range-1 → ParseTreeT
  parsed-alpha-range-2 : alpha-range-2 → ParseTreeT
  parsed-bvar : bvar → ParseTreeT
  parsed-bvar-bar-13 : bvar-bar-13 → ParseTreeT
  parsed-fpth : fpth → ParseTreeT
  parsed-fpth-bar-15 : fpth-bar-15 → ParseTreeT
  parsed-fpth-bar-16 : fpth-bar-16 → ParseTreeT
  parsed-fpth-bar-17 : fpth-bar-17 → ParseTreeT
  parsed-fpth-plus-14 : fpth-plus-14 → ParseTreeT
  parsed-fpth-star-18 : fpth-star-18 → ParseTreeT
  parsed-kvar : kvar → ParseTreeT
  parsed-kvar-bar-19 : kvar-bar-19 → ParseTreeT
  parsed-kvar-star-20 : kvar-star-20 → ParseTreeT
  parsed-num : num → ParseTreeT
  parsed-num-plus-5 : num-plus-5 → ParseTreeT
  parsed-numone : numone → ParseTreeT
  parsed-numone-range-4 : numone-range-4 → ParseTreeT
  parsed-numpunct : numpunct → ParseTreeT
  parsed-numpunct-bar-10 : numpunct-bar-10 → ParseTreeT
  parsed-numpunct-bar-6 : numpunct-bar-6 → ParseTreeT
  parsed-numpunct-bar-7 : numpunct-bar-7 → ParseTreeT
  parsed-numpunct-bar-8 : numpunct-bar-8 → ParseTreeT
  parsed-numpunct-bar-9 : numpunct-bar-9 → ParseTreeT
  parsed-qkvar : qkvar → ParseTreeT
  parsed-qvar : qvar → ParseTreeT
  parsed-var : var → ParseTreeT
  parsed-var-bar-11 : var-bar-11 → ParseTreeT
  parsed-var-star-12 : var-star-12 → ParseTreeT
  parsed-anychar : ParseTreeT
  parsed-anychar-bar-68 : ParseTreeT
  parsed-anychar-bar-69 : ParseTreeT
  parsed-anychar-bar-70 : ParseTreeT
  parsed-anychar-bar-71 : ParseTreeT
  parsed-anychar-bar-72 : ParseTreeT
  parsed-aws : ParseTreeT
  parsed-aws-bar-74 : ParseTreeT
  parsed-aws-bar-75 : ParseTreeT
  parsed-aws-bar-76 : ParseTreeT
  parsed-comment : ParseTreeT
  parsed-comment-star-73 : ParseTreeT
  parsed-otherpunct : ParseTreeT
  parsed-otherpunct-bar-21 : ParseTreeT
  parsed-otherpunct-bar-22 : ParseTreeT
  parsed-otherpunct-bar-23 : ParseTreeT
  parsed-otherpunct-bar-24 : ParseTreeT
  parsed-otherpunct-bar-25 : ParseTreeT
  parsed-otherpunct-bar-26 : ParseTreeT
  parsed-otherpunct-bar-27 : ParseTreeT
  parsed-otherpunct-bar-28 : ParseTreeT
  parsed-otherpunct-bar-29 : ParseTreeT
  parsed-otherpunct-bar-30 : ParseTreeT
  parsed-otherpunct-bar-31 : ParseTreeT
  parsed-otherpunct-bar-32 : ParseTreeT
  parsed-otherpunct-bar-33 : ParseTreeT
  parsed-otherpunct-bar-34 : ParseTreeT
  parsed-otherpunct-bar-35 : ParseTreeT
  parsed-otherpunct-bar-36 : ParseTreeT
  parsed-otherpunct-bar-37 : ParseTreeT
  parsed-otherpunct-bar-38 : ParseTreeT
  parsed-otherpunct-bar-39 : ParseTreeT
  parsed-otherpunct-bar-40 : ParseTreeT
  parsed-otherpunct-bar-41 : ParseTreeT
  parsed-otherpunct-bar-42 : ParseTreeT
  parsed-otherpunct-bar-43 : ParseTreeT
  parsed-otherpunct-bar-44 : ParseTreeT
  parsed-otherpunct-bar-45 : ParseTreeT
  parsed-otherpunct-bar-46 : ParseTreeT
  parsed-otherpunct-bar-47 : ParseTreeT
  parsed-otherpunct-bar-48 : ParseTreeT
  parsed-otherpunct-bar-49 : ParseTreeT
  parsed-otherpunct-bar-50 : ParseTreeT
  parsed-otherpunct-bar-51 : ParseTreeT
  parsed-otherpunct-bar-52 : ParseTreeT
  parsed-otherpunct-bar-53 : ParseTreeT
  parsed-otherpunct-bar-54 : ParseTreeT
  parsed-otherpunct-bar-55 : ParseTreeT
  parsed-otherpunct-bar-56 : ParseTreeT
  parsed-otherpunct-bar-57 : ParseTreeT
  parsed-otherpunct-bar-58 : ParseTreeT
  parsed-otherpunct-bar-59 : ParseTreeT
  parsed-otherpunct-bar-60 : ParseTreeT
  parsed-otherpunct-bar-61 : ParseTreeT
  parsed-otherpunct-bar-62 : ParseTreeT
  parsed-otherpunct-bar-63 : ParseTreeT
  parsed-otherpunct-bar-64 : ParseTreeT
  parsed-otherpunct-bar-65 : ParseTreeT
  parsed-otherpunct-bar-66 : ParseTreeT
  parsed-otherpunct-bar-67 : ParseTreeT
  parsed-ows : ParseTreeT
  parsed-ows-star-78 : ParseTreeT
  parsed-ws : ParseTreeT
  parsed-ws-plus-77 : ParseTreeT

------------------------------------------
-- Parse tree printing functions
------------------------------------------

posinfoToString : posinfo → string
posinfoToString x = "(posinfo " ^ x ^ ")"
alphaToString : alpha → string
alphaToString x = "(alpha " ^ x ^ ")"
alpha-bar-3ToString : alpha-bar-3 → string
alpha-bar-3ToString x = "(alpha-bar-3 " ^ x ^ ")"
alpha-range-1ToString : alpha-range-1 → string
alpha-range-1ToString x = "(alpha-range-1 " ^ x ^ ")"
alpha-range-2ToString : alpha-range-2 → string
alpha-range-2ToString x = "(alpha-range-2 " ^ x ^ ")"
bvarToString : bvar → string
bvarToString x = "(bvar " ^ x ^ ")"
bvar-bar-13ToString : bvar-bar-13 → string
bvar-bar-13ToString x = "(bvar-bar-13 " ^ x ^ ")"
fpthToString : fpth → string
fpthToString x = "(fpth " ^ x ^ ")"
fpth-bar-15ToString : fpth-bar-15 → string
fpth-bar-15ToString x = "(fpth-bar-15 " ^ x ^ ")"
fpth-bar-16ToString : fpth-bar-16 → string
fpth-bar-16ToString x = "(fpth-bar-16 " ^ x ^ ")"
fpth-bar-17ToString : fpth-bar-17 → string
fpth-bar-17ToString x = "(fpth-bar-17 " ^ x ^ ")"
fpth-plus-14ToString : fpth-plus-14 → string
fpth-plus-14ToString x = "(fpth-plus-14 " ^ x ^ ")"
fpth-star-18ToString : fpth-star-18 → string
fpth-star-18ToString x = "(fpth-star-18 " ^ x ^ ")"
kvarToString : kvar → string
kvarToString x = "(kvar " ^ x ^ ")"
kvar-bar-19ToString : kvar-bar-19 → string
kvar-bar-19ToString x = "(kvar-bar-19 " ^ x ^ ")"
kvar-star-20ToString : kvar-star-20 → string
kvar-star-20ToString x = "(kvar-star-20 " ^ x ^ ")"
numToString : num → string
numToString x = "(num " ^ x ^ ")"
num-plus-5ToString : num-plus-5 → string
num-plus-5ToString x = "(num-plus-5 " ^ x ^ ")"
numoneToString : numone → string
numoneToString x = "(numone " ^ x ^ ")"
numone-range-4ToString : numone-range-4 → string
numone-range-4ToString x = "(numone-range-4 " ^ x ^ ")"
numpunctToString : numpunct → string
numpunctToString x = "(numpunct " ^ x ^ ")"
numpunct-bar-10ToString : numpunct-bar-10 → string
numpunct-bar-10ToString x = "(numpunct-bar-10 " ^ x ^ ")"
numpunct-bar-6ToString : numpunct-bar-6 → string
numpunct-bar-6ToString x = "(numpunct-bar-6 " ^ x ^ ")"
numpunct-bar-7ToString : numpunct-bar-7 → string
numpunct-bar-7ToString x = "(numpunct-bar-7 " ^ x ^ ")"
numpunct-bar-8ToString : numpunct-bar-8 → string
numpunct-bar-8ToString x = "(numpunct-bar-8 " ^ x ^ ")"
numpunct-bar-9ToString : numpunct-bar-9 → string
numpunct-bar-9ToString x = "(numpunct-bar-9 " ^ x ^ ")"
qkvarToString : qkvar → string
qkvarToString x = "(qkvar " ^ x ^ ")"
qvarToString : qvar → string
qvarToString x = "(qvar " ^ x ^ ")"
varToString : var → string
varToString x = "(var " ^ x ^ ")"
var-bar-11ToString : var-bar-11 → string
var-bar-11ToString x = "(var-bar-11 " ^ x ^ ")"
var-star-12ToString : var-star-12 → string
var-star-12ToString x = "(var-star-12 " ^ x ^ ")"

mutual
  argToString : arg → string
  argToString (TermArg x0) = "(TermArg" ^ " " ^ (termToString x0) ^ ")"
  argToString (TypeArg x0) = "(TypeArg" ^ " " ^ (typeToString x0) ^ ")"

  argsToString : args → string
  argsToString (ArgsCons x0 x1) = "(ArgsCons" ^ " " ^ (argToString x0) ^ " " ^ (argsToString x1) ^ ")"
  argsToString (ArgsNil x0) = "(ArgsNil" ^ " " ^ (posinfoToString x0) ^ ")"

  arrowtypeToString : arrowtype → string
  arrowtypeToString (ErasedArrow) = "ErasedArrow" ^ ""
  arrowtypeToString (UnerasedArrow) = "UnerasedArrow" ^ ""

  binderToString : binder → string
  binderToString (All) = "All" ^ ""
  binderToString (Pi) = "Pi" ^ ""

  cmdToString : cmd → string
  cmdToString (DefKind x0 x1 x2 x3 x4) = "(DefKind" ^ " " ^ (posinfoToString x0) ^ " " ^ (kvarToString x1) ^ " " ^ (paramsToString x2) ^ " " ^ (kindToString x3) ^ " " ^ (posinfoToString x4) ^ ")"
  cmdToString (DefTermOrType x0 x1) = "(DefTermOrType" ^ " " ^ (defTermOrTypeToString x0) ^ " " ^ (posinfoToString x1) ^ ")"
  cmdToString (ImportCmd x0) = "(ImportCmd" ^ " " ^ (imprtToString x0) ^ ")"

  cmdsToString : cmds → string
  cmdsToString (CmdsNext x0 x1) = "(CmdsNext" ^ " " ^ (cmdToString x0) ^ " " ^ (cmdsToString x1) ^ ")"
  cmdsToString (CmdsStart) = "CmdsStart" ^ ""

  declToString : decl → string
  declToString (Decl x0 x1 x2 x3 x4) = "(Decl" ^ " " ^ (posinfoToString x0) ^ " " ^ (posinfoToString x1) ^ " " ^ (bvarToString x2) ^ " " ^ (tkToString x3) ^ " " ^ (posinfoToString x4) ^ ")"

  defTermOrTypeToString : defTermOrType → string
  defTermOrTypeToString (DefTerm x0 x1 x2 x3) = "(DefTerm" ^ " " ^ (posinfoToString x0) ^ " " ^ (varToString x1) ^ " " ^ (maybeCheckTypeToString x2) ^ " " ^ (termToString x3) ^ ")"
  defTermOrTypeToString (DefType x0 x1 x2 x3) = "(DefType" ^ " " ^ (posinfoToString x0) ^ " " ^ (varToString x1) ^ " " ^ (kindToString x2) ^ " " ^ (typeToString x3) ^ ")"

  importsToString : imports → string
  importsToString (ImportsNext x0 x1) = "(ImportsNext" ^ " " ^ (imprtToString x0) ^ " " ^ (importsToString x1) ^ ")"
  importsToString (ImportsStart) = "ImportsStart" ^ ""

  imprtToString : imprt → string
  imprtToString (Import x0 x1 x2 x3 x4) = "(Import" ^ " " ^ (posinfoToString x0) ^ " " ^ (fpthToString x1) ^ " " ^ (optAsToString x2) ^ " " ^ (argsToString x3) ^ " " ^ (posinfoToString x4) ^ ")"

  kindToString : kind → string
  kindToString (KndArrow x0 x1) = "(KndArrow" ^ " " ^ (kindToString x0) ^ " " ^ (kindToString x1) ^ ")"
  kindToString (KndParens x0 x1 x2) = "(KndParens" ^ " " ^ (posinfoToString x0) ^ " " ^ (kindToString x1) ^ " " ^ (posinfoToString x2) ^ ")"
  kindToString (KndPi x0 x1 x2 x3 x4) = "(KndPi" ^ " " ^ (posinfoToString x0) ^ " " ^ (posinfoToString x1) ^ " " ^ (bvarToString x2) ^ " " ^ (tkToString x3) ^ " " ^ (kindToString x4) ^ ")"
  kindToString (KndTpArrow x0 x1) = "(KndTpArrow" ^ " " ^ (typeToString x0) ^ " " ^ (kindToString x1) ^ ")"
  kindToString (KndVar x0 x1 x2) = "(KndVar" ^ " " ^ (posinfoToString x0) ^ " " ^ (qkvarToString x1) ^ " " ^ (argsToString x2) ^ ")"
  kindToString (Star x0) = "(Star" ^ " " ^ (posinfoToString x0) ^ ")"

  lamToString : lam → string
  lamToString (ErasedLambda) = "ErasedLambda" ^ ""
  lamToString (KeptLambda) = "KeptLambda" ^ ""

  leftRightToString : leftRight → string
  leftRightToString (Both) = "Both" ^ ""
  leftRightToString (Left) = "Left" ^ ""
  leftRightToString (Right) = "Right" ^ ""

  liftingTypeToString : liftingType → string
  liftingTypeToString (LiftArrow x0 x1) = "(LiftArrow" ^ " " ^ (liftingTypeToString x0) ^ " " ^ (liftingTypeToString x1) ^ ")"
  liftingTypeToString (LiftParens x0 x1 x2) = "(LiftParens" ^ " " ^ (posinfoToString x0) ^ " " ^ (liftingTypeToString x1) ^ " " ^ (posinfoToString x2) ^ ")"
  liftingTypeToString (LiftPi x0 x1 x2 x3) = "(LiftPi" ^ " " ^ (posinfoToString x0) ^ " " ^ (bvarToString x1) ^ " " ^ (typeToString x2) ^ " " ^ (liftingTypeToString x3) ^ ")"
  liftingTypeToString (LiftStar x0) = "(LiftStar" ^ " " ^ (posinfoToString x0) ^ ")"
  liftingTypeToString (LiftTpArrow x0 x1) = "(LiftTpArrow" ^ " " ^ (typeToString x0) ^ " " ^ (liftingTypeToString x1) ^ ")"

  ltermsToString : lterms → string
  ltermsToString (LtermsCons x0 x1 x2) = "(LtermsCons" ^ " " ^ (maybeErasedToString x0) ^ " " ^ (termToString x1) ^ " " ^ (ltermsToString x2) ^ ")"
  ltermsToString (LtermsNil x0) = "(LtermsNil" ^ " " ^ (posinfoToString x0) ^ ")"

  maybeAtypeToString : maybeAtype → string
  maybeAtypeToString (Atype x0) = "(Atype" ^ " " ^ (typeToString x0) ^ ")"
  maybeAtypeToString (NoAtype) = "NoAtype" ^ ""

  maybeCheckTypeToString : maybeCheckType → string
  maybeCheckTypeToString (NoCheckType) = "NoCheckType" ^ ""
  maybeCheckTypeToString (Type x0) = "(Type" ^ " " ^ (typeToString x0) ^ ")"

  maybeErasedToString : maybeErased → string
  maybeErasedToString (Erased) = "Erased" ^ ""
  maybeErasedToString (NotErased) = "NotErased" ^ ""

  maybeMinusToString : maybeMinus → string
  maybeMinusToString (EpsHanf) = "EpsHanf" ^ ""
  maybeMinusToString (EpsHnf) = "EpsHnf" ^ ""

  optAsToString : optAs → string
  optAsToString (NoOptAs) = "NoOptAs" ^ ""
  optAsToString (SomeOptAs x0) = "(SomeOptAs" ^ " " ^ (varToString x0) ^ ")"

  optClassToString : optClass → string
  optClassToString (NoClass) = "NoClass" ^ ""
  optClassToString (SomeClass x0) = "(SomeClass" ^ " " ^ (tkToString x0) ^ ")"

  optTermToString : optTerm → string
  optTermToString (NoTerm) = "NoTerm" ^ ""
  optTermToString (SomeTerm x0 x1) = "(SomeTerm" ^ " " ^ (termToString x0) ^ " " ^ (posinfoToString x1) ^ ")"

  optTypeToString : optType → string
  optTypeToString (NoType) = "NoType" ^ ""
  optTypeToString (SomeType x0) = "(SomeType" ^ " " ^ (typeToString x0) ^ ")"

  paramsToString : params → string
  paramsToString (ParamsCons x0 x1) = "(ParamsCons" ^ " " ^ (declToString x0) ^ " " ^ (paramsToString x1) ^ ")"
  paramsToString (ParamsNil) = "ParamsNil" ^ ""

  rhoToString : rho → string
  rhoToString (RhoPlain) = "RhoPlain" ^ ""
  rhoToString (RhoPlus) = "RhoPlus" ^ ""

  startToString : start → string
  startToString (File x0 x1 x2 x3 x4 x5) = "(File" ^ " " ^ (posinfoToString x0) ^ " " ^ (importsToString x1) ^ " " ^ (qvarToString x2) ^ " " ^ (paramsToString x3) ^ " " ^ (cmdsToString x4) ^ " " ^ (posinfoToString x5) ^ ")"

  termToString : term → string
  termToString (App x0 x1 x2) = "(App" ^ " " ^ (termToString x0) ^ " " ^ (maybeErasedToString x1) ^ " " ^ (termToString x2) ^ ")"
  termToString (AppTp x0 x1) = "(AppTp" ^ " " ^ (termToString x0) ^ " " ^ (typeToString x1) ^ ")"
  termToString (Beta x0 x1) = "(Beta" ^ " " ^ (posinfoToString x0) ^ " " ^ (optTermToString x1) ^ ")"
  termToString (Chi x0 x1 x2) = "(Chi" ^ " " ^ (posinfoToString x0) ^ " " ^ (maybeAtypeToString x1) ^ " " ^ (termToString x2) ^ ")"
  termToString (Epsilon x0 x1 x2 x3) = "(Epsilon" ^ " " ^ (posinfoToString x0) ^ " " ^ (leftRightToString x1) ^ " " ^ (maybeMinusToString x2) ^ " " ^ (termToString x3) ^ ")"
  termToString (Hole x0) = "(Hole" ^ " " ^ (posinfoToString x0) ^ ")"
  termToString (IotaPair x0 x1 x2 x3 x4) = "(IotaPair" ^ " " ^ (posinfoToString x0) ^ " " ^ (termToString x1) ^ " " ^ (termToString x2) ^ " " ^ (optTermToString x3) ^ " " ^ (posinfoToString x4) ^ ")"
  termToString (IotaProj x0 x1 x2) = "(IotaProj" ^ " " ^ (termToString x0) ^ " " ^ (numToString x1) ^ " " ^ (posinfoToString x2) ^ ")"
  termToString (Lam x0 x1 x2 x3 x4 x5) = "(Lam" ^ " " ^ (posinfoToString x0) ^ " " ^ (lamToString x1) ^ " " ^ (posinfoToString x2) ^ " " ^ (bvarToString x3) ^ " " ^ (optClassToString x4) ^ " " ^ (termToString x5) ^ ")"
  termToString (Let x0 x1 x2) = "(Let" ^ " " ^ (posinfoToString x0) ^ " " ^ (defTermOrTypeToString x1) ^ " " ^ (termToString x2) ^ ")"
  termToString (Parens x0 x1 x2) = "(Parens" ^ " " ^ (posinfoToString x0) ^ " " ^ (termToString x1) ^ " " ^ (posinfoToString x2) ^ ")"
  termToString (Rho x0 x1 x2 x3) = "(Rho" ^ " " ^ (posinfoToString x0) ^ " " ^ (rhoToString x1) ^ " " ^ (termToString x2) ^ " " ^ (termToString x3) ^ ")"
  termToString (Sigma x0 x1) = "(Sigma" ^ " " ^ (posinfoToString x0) ^ " " ^ (termToString x1) ^ ")"
  termToString (Theta x0 x1 x2 x3) = "(Theta" ^ " " ^ (posinfoToString x0) ^ " " ^ (thetaToString x1) ^ " " ^ (termToString x2) ^ " " ^ (ltermsToString x3) ^ ")"
  termToString (Var x0 x1) = "(Var" ^ " " ^ (posinfoToString x0) ^ " " ^ (qvarToString x1) ^ ")"

  thetaToString : theta → string
  thetaToString (Abstract) = "Abstract" ^ ""
  thetaToString (AbstractEq) = "AbstractEq" ^ ""
  thetaToString (AbstractVars x0) = "(AbstractVars" ^ " " ^ (varsToString x0) ^ ")"

  tkToString : tk → string
  tkToString (Tkk x0) = "(Tkk" ^ " " ^ (kindToString x0) ^ ")"
  tkToString (Tkt x0) = "(Tkt" ^ " " ^ (typeToString x0) ^ ")"

  typeToString : type → string
  typeToString (Abs x0 x1 x2 x3 x4 x5) = "(Abs" ^ " " ^ (posinfoToString x0) ^ " " ^ (binderToString x1) ^ " " ^ (posinfoToString x2) ^ " " ^ (bvarToString x3) ^ " " ^ (tkToString x4) ^ " " ^ (typeToString x5) ^ ")"
  typeToString (Iota x0 x1 x2 x3 x4) = "(Iota" ^ " " ^ (posinfoToString x0) ^ " " ^ (posinfoToString x1) ^ " " ^ (bvarToString x2) ^ " " ^ (optTypeToString x3) ^ " " ^ (typeToString x4) ^ ")"
  typeToString (Lft x0 x1 x2 x3 x4) = "(Lft" ^ " " ^ (posinfoToString x0) ^ " " ^ (posinfoToString x1) ^ " " ^ (varToString x2) ^ " " ^ (termToString x3) ^ " " ^ (liftingTypeToString x4) ^ ")"
  typeToString (NoSpans x0 x1) = "(NoSpans" ^ " " ^ (typeToString x0) ^ " " ^ (posinfoToString x1) ^ ")"
  typeToString (TpApp x0 x1) = "(TpApp" ^ " " ^ (typeToString x0) ^ " " ^ (typeToString x1) ^ ")"
  typeToString (TpAppt x0 x1) = "(TpAppt" ^ " " ^ (typeToString x0) ^ " " ^ (termToString x1) ^ ")"
  typeToString (TpArrow x0 x1 x2) = "(TpArrow" ^ " " ^ (typeToString x0) ^ " " ^ (arrowtypeToString x1) ^ " " ^ (typeToString x2) ^ ")"
  typeToString (TpEq x0 x1) = "(TpEq" ^ " " ^ (termToString x0) ^ " " ^ (termToString x1) ^ ")"
  typeToString (TpHole x0) = "(TpHole" ^ " " ^ (posinfoToString x0) ^ ")"
  typeToString (TpLambda x0 x1 x2 x3 x4) = "(TpLambda" ^ " " ^ (posinfoToString x0) ^ " " ^ (posinfoToString x1) ^ " " ^ (bvarToString x2) ^ " " ^ (tkToString x3) ^ " " ^ (typeToString x4) ^ ")"
  typeToString (TpParens x0 x1 x2) = "(TpParens" ^ " " ^ (posinfoToString x0) ^ " " ^ (typeToString x1) ^ " " ^ (posinfoToString x2) ^ ")"
  typeToString (TpVar x0 x1) = "(TpVar" ^ " " ^ (posinfoToString x0) ^ " " ^ (qvarToString x1) ^ ")"

  varsToString : vars → string
  varsToString (VarsNext x0 x1) = "(VarsNext" ^ " " ^ (varToString x0) ^ " " ^ (varsToString x1) ^ ")"
  varsToString (VarsStart x0) = "(VarsStart" ^ " " ^ (varToString x0) ^ ")"

ParseTreeToString : ParseTreeT → string
ParseTreeToString (parsed-arg t) = argToString t
ParseTreeToString (parsed-args t) = argsToString t
ParseTreeToString (parsed-arrowtype t) = arrowtypeToString t
ParseTreeToString (parsed-binder t) = binderToString t
ParseTreeToString (parsed-cmd t) = cmdToString t
ParseTreeToString (parsed-cmds t) = cmdsToString t
ParseTreeToString (parsed-decl t) = declToString t
ParseTreeToString (parsed-defTermOrType t) = defTermOrTypeToString t
ParseTreeToString (parsed-imports t) = importsToString t
ParseTreeToString (parsed-imprt t) = imprtToString t
ParseTreeToString (parsed-kind t) = kindToString t
ParseTreeToString (parsed-lam t) = lamToString t
ParseTreeToString (parsed-leftRight t) = leftRightToString t
ParseTreeToString (parsed-liftingType t) = liftingTypeToString t
ParseTreeToString (parsed-lterms t) = ltermsToString t
ParseTreeToString (parsed-maybeAtype t) = maybeAtypeToString t
ParseTreeToString (parsed-maybeCheckType t) = maybeCheckTypeToString t
ParseTreeToString (parsed-maybeErased t) = maybeErasedToString t
ParseTreeToString (parsed-maybeMinus t) = maybeMinusToString t
ParseTreeToString (parsed-optAs t) = optAsToString t
ParseTreeToString (parsed-optClass t) = optClassToString t
ParseTreeToString (parsed-optTerm t) = optTermToString t
ParseTreeToString (parsed-optType t) = optTypeToString t
ParseTreeToString (parsed-params t) = paramsToString t
ParseTreeToString (parsed-rho t) = rhoToString t
ParseTreeToString (parsed-start t) = startToString t
ParseTreeToString (parsed-term t) = termToString t
ParseTreeToString (parsed-theta t) = thetaToString t
ParseTreeToString (parsed-tk t) = tkToString t
ParseTreeToString (parsed-type t) = typeToString t
ParseTreeToString (parsed-vars t) = varsToString t
ParseTreeToString (parsed-aterm t) = termToString t
ParseTreeToString (parsed-atype t) = typeToString t
ParseTreeToString (parsed-lliftingType t) = liftingTypeToString t
ParseTreeToString (parsed-lterm t) = termToString t
ParseTreeToString (parsed-ltype t) = typeToString t
ParseTreeToString (parsed-pterm t) = termToString t
ParseTreeToString (parsed-posinfo t) = posinfoToString t
ParseTreeToString (parsed-alpha t) = alphaToString t
ParseTreeToString (parsed-alpha-bar-3 t) = alpha-bar-3ToString t
ParseTreeToString (parsed-alpha-range-1 t) = alpha-range-1ToString t
ParseTreeToString (parsed-alpha-range-2 t) = alpha-range-2ToString t
ParseTreeToString (parsed-bvar t) = bvarToString t
ParseTreeToString (parsed-bvar-bar-13 t) = bvar-bar-13ToString t
ParseTreeToString (parsed-fpth t) = fpthToString t
ParseTreeToString (parsed-fpth-bar-15 t) = fpth-bar-15ToString t
ParseTreeToString (parsed-fpth-bar-16 t) = fpth-bar-16ToString t
ParseTreeToString (parsed-fpth-bar-17 t) = fpth-bar-17ToString t
ParseTreeToString (parsed-fpth-plus-14 t) = fpth-plus-14ToString t
ParseTreeToString (parsed-fpth-star-18 t) = fpth-star-18ToString t
ParseTreeToString (parsed-kvar t) = kvarToString t
ParseTreeToString (parsed-kvar-bar-19 t) = kvar-bar-19ToString t
ParseTreeToString (parsed-kvar-star-20 t) = kvar-star-20ToString t
ParseTreeToString (parsed-num t) = numToString t
ParseTreeToString (parsed-num-plus-5 t) = num-plus-5ToString t
ParseTreeToString (parsed-numone t) = numoneToString t
ParseTreeToString (parsed-numone-range-4 t) = numone-range-4ToString t
ParseTreeToString (parsed-numpunct t) = numpunctToString t
ParseTreeToString (parsed-numpunct-bar-10 t) = numpunct-bar-10ToString t
ParseTreeToString (parsed-numpunct-bar-6 t) = numpunct-bar-6ToString t
ParseTreeToString (parsed-numpunct-bar-7 t) = numpunct-bar-7ToString t
ParseTreeToString (parsed-numpunct-bar-8 t) = numpunct-bar-8ToString t
ParseTreeToString (parsed-numpunct-bar-9 t) = numpunct-bar-9ToString t
ParseTreeToString (parsed-qkvar t) = qkvarToString t
ParseTreeToString (parsed-qvar t) = qvarToString t
ParseTreeToString (parsed-var t) = varToString t
ParseTreeToString (parsed-var-bar-11 t) = var-bar-11ToString t
ParseTreeToString (parsed-var-star-12 t) = var-star-12ToString t
ParseTreeToString parsed-anychar = "[anychar]"
ParseTreeToString parsed-anychar-bar-68 = "[anychar-bar-68]"
ParseTreeToString parsed-anychar-bar-69 = "[anychar-bar-69]"
ParseTreeToString parsed-anychar-bar-70 = "[anychar-bar-70]"
ParseTreeToString parsed-anychar-bar-71 = "[anychar-bar-71]"
ParseTreeToString parsed-anychar-bar-72 = "[anychar-bar-72]"
ParseTreeToString parsed-aws = "[aws]"
ParseTreeToString parsed-aws-bar-74 = "[aws-bar-74]"
ParseTreeToString parsed-aws-bar-75 = "[aws-bar-75]"
ParseTreeToString parsed-aws-bar-76 = "[aws-bar-76]"
ParseTreeToString parsed-comment = "[comment]"
ParseTreeToString parsed-comment-star-73 = "[comment-star-73]"
ParseTreeToString parsed-otherpunct = "[otherpunct]"
ParseTreeToString parsed-otherpunct-bar-21 = "[otherpunct-bar-21]"
ParseTreeToString parsed-otherpunct-bar-22 = "[otherpunct-bar-22]"
ParseTreeToString parsed-otherpunct-bar-23 = "[otherpunct-bar-23]"
ParseTreeToString parsed-otherpunct-bar-24 = "[otherpunct-bar-24]"
ParseTreeToString parsed-otherpunct-bar-25 = "[otherpunct-bar-25]"
ParseTreeToString parsed-otherpunct-bar-26 = "[otherpunct-bar-26]"
ParseTreeToString parsed-otherpunct-bar-27 = "[otherpunct-bar-27]"
ParseTreeToString parsed-otherpunct-bar-28 = "[otherpunct-bar-28]"
ParseTreeToString parsed-otherpunct-bar-29 = "[otherpunct-bar-29]"
ParseTreeToString parsed-otherpunct-bar-30 = "[otherpunct-bar-30]"
ParseTreeToString parsed-otherpunct-bar-31 = "[otherpunct-bar-31]"
ParseTreeToString parsed-otherpunct-bar-32 = "[otherpunct-bar-32]"
ParseTreeToString parsed-otherpunct-bar-33 = "[otherpunct-bar-33]"
ParseTreeToString parsed-otherpunct-bar-34 = "[otherpunct-bar-34]"
ParseTreeToString parsed-otherpunct-bar-35 = "[otherpunct-bar-35]"
ParseTreeToString parsed-otherpunct-bar-36 = "[otherpunct-bar-36]"
ParseTreeToString parsed-otherpunct-bar-37 = "[otherpunct-bar-37]"
ParseTreeToString parsed-otherpunct-bar-38 = "[otherpunct-bar-38]"
ParseTreeToString parsed-otherpunct-bar-39 = "[otherpunct-bar-39]"
ParseTreeToString parsed-otherpunct-bar-40 = "[otherpunct-bar-40]"
ParseTreeToString parsed-otherpunct-bar-41 = "[otherpunct-bar-41]"
ParseTreeToString parsed-otherpunct-bar-42 = "[otherpunct-bar-42]"
ParseTreeToString parsed-otherpunct-bar-43 = "[otherpunct-bar-43]"
ParseTreeToString parsed-otherpunct-bar-44 = "[otherpunct-bar-44]"
ParseTreeToString parsed-otherpunct-bar-45 = "[otherpunct-bar-45]"
ParseTreeToString parsed-otherpunct-bar-46 = "[otherpunct-bar-46]"
ParseTreeToString parsed-otherpunct-bar-47 = "[otherpunct-bar-47]"
ParseTreeToString parsed-otherpunct-bar-48 = "[otherpunct-bar-48]"
ParseTreeToString parsed-otherpunct-bar-49 = "[otherpunct-bar-49]"
ParseTreeToString parsed-otherpunct-bar-50 = "[otherpunct-bar-50]"
ParseTreeToString parsed-otherpunct-bar-51 = "[otherpunct-bar-51]"
ParseTreeToString parsed-otherpunct-bar-52 = "[otherpunct-bar-52]"
ParseTreeToString parsed-otherpunct-bar-53 = "[otherpunct-bar-53]"
ParseTreeToString parsed-otherpunct-bar-54 = "[otherpunct-bar-54]"
ParseTreeToString parsed-otherpunct-bar-55 = "[otherpunct-bar-55]"
ParseTreeToString parsed-otherpunct-bar-56 = "[otherpunct-bar-56]"
ParseTreeToString parsed-otherpunct-bar-57 = "[otherpunct-bar-57]"
ParseTreeToString parsed-otherpunct-bar-58 = "[otherpunct-bar-58]"
ParseTreeToString parsed-otherpunct-bar-59 = "[otherpunct-bar-59]"
ParseTreeToString parsed-otherpunct-bar-60 = "[otherpunct-bar-60]"
ParseTreeToString parsed-otherpunct-bar-61 = "[otherpunct-bar-61]"
ParseTreeToString parsed-otherpunct-bar-62 = "[otherpunct-bar-62]"
ParseTreeToString parsed-otherpunct-bar-63 = "[otherpunct-bar-63]"
ParseTreeToString parsed-otherpunct-bar-64 = "[otherpunct-bar-64]"
ParseTreeToString parsed-otherpunct-bar-65 = "[otherpunct-bar-65]"
ParseTreeToString parsed-otherpunct-bar-66 = "[otherpunct-bar-66]"
ParseTreeToString parsed-otherpunct-bar-67 = "[otherpunct-bar-67]"
ParseTreeToString parsed-ows = "[ows]"
ParseTreeToString parsed-ows-star-78 = "[ows-star-78]"
ParseTreeToString parsed-ws = "[ws]"
ParseTreeToString parsed-ws-plus-77 = "[ws-plus-77]"

------------------------------------------
-- Reorganizing rules
------------------------------------------

mutual

  {-# TERMINATING #-}
  norm-vars : (x : vars) → vars
  norm-vars x = x

  {-# TERMINATING #-}
  norm-type : (x : type) → type
  norm-type (TpApp x1 (TpAppt x2 x3)) = (norm-type (TpAppt  (norm-type (TpApp  x1 x2) ) x3) )
  norm-type (TpApp x1 (TpApp x2 x3)) = (norm-type (TpApp  (norm-type (TpApp  x1 x2) ) x3) )
  norm-type x = x

  {-# TERMINATING #-}
  norm-tk : (x : tk) → tk
  norm-tk x = x

  {-# TERMINATING #-}
  norm-theta : (x : theta) → theta
  norm-theta x = x

  {-# TERMINATING #-}
  norm-term : (x : term) → term
  norm-term (AppTp (App x1 x2 (Lam x3 x4 x5 x6 x7 x8)) x9) = (norm-term (App  x1 x2 (norm-term (Lam  x3 x4 x5 x6 x7 (norm-term (AppTp  x8 x9) )) )) )
  norm-term (AppTp (Lam x1 x2 x3 x4 x5 x6) x7) = (norm-term (Lam  x1 x2 x3 x4 x5 (norm-term (AppTp  x6 x7) )) )
  norm-term (App x1 x2 (AppTp x3 x4)) = (norm-term (AppTp  (norm-term (App  x1 x2 x3) ) x4) )
  norm-term (App (App x1 x2 (Lam x3 x4 x5 x6 x7 x8)) x9 x10) = (norm-term (App  x1 x2 (norm-term (Lam  x3 x4 x5 x6 x7 (norm-term (App  x8 x9 x10) )) )) )
  norm-term (App (Lam x1 x2 x3 x4 x5 x6) x7 x8) = (norm-term (Lam  x1 x2 x3 x4 x5 (norm-term (App  x6 x7 x8) )) )
  norm-term (App x1 x2 (App x3 x4 x5)) = (norm-term (App  (norm-term (App  x1 x2 x3) ) x4 x5) )
  norm-term x = x

  {-# TERMINATING #-}
  norm-start : (x : start) → start
  norm-start x = x

  {-# TERMINATING #-}
  norm-rho : (x : rho) → rho
  norm-rho x = x

  {-# TERMINATING #-}
  norm-pterm : (x : pterm) → pterm
  norm-pterm x = x

  {-# TERMINATING #-}
  norm-posinfo : (x : posinfo) → posinfo
  norm-posinfo x = x

  {-# TERMINATING #-}
  norm-params : (x : params) → params
  norm-params x = x

  {-# TERMINATING #-}
  norm-optType : (x : optType) → optType
  norm-optType x = x

  {-# TERMINATING #-}
  norm-optTerm : (x : optTerm) → optTerm
  norm-optTerm x = x

  {-# TERMINATING #-}
  norm-optClass : (x : optClass) → optClass
  norm-optClass x = x

  {-# TERMINATING #-}
  norm-optAs : (x : optAs) → optAs
  norm-optAs x = x

  {-# TERMINATING #-}
  norm-maybeMinus : (x : maybeMinus) → maybeMinus
  norm-maybeMinus x = x

  {-# TERMINATING #-}
  norm-maybeErased : (x : maybeErased) → maybeErased
  norm-maybeErased x = x

  {-# TERMINATING #-}
  norm-maybeCheckType : (x : maybeCheckType) → maybeCheckType
  norm-maybeCheckType x = x

  {-# TERMINATING #-}
  norm-maybeAtype : (x : maybeAtype) → maybeAtype
  norm-maybeAtype x = x

  {-# TERMINATING #-}
  norm-ltype : (x : ltype) → ltype
  norm-ltype x = x

  {-# TERMINATING #-}
  norm-lterms : (x : lterms) → lterms
  norm-lterms x = x

  {-# TERMINATING #-}
  norm-lterm : (x : lterm) → lterm
  norm-lterm x = x

  {-# TERMINATING #-}
  norm-lliftingType : (x : lliftingType) → lliftingType
  norm-lliftingType x = x

  {-# TERMINATING #-}
  norm-liftingType : (x : liftingType) → liftingType
  norm-liftingType (LiftArrow (LiftPi x1 x2 x3 x4) x5) = (norm-liftingType (LiftPi  x1 x2 x3 (norm-liftingType (LiftArrow  x4 x5) )) )
  norm-liftingType (LiftTpArrow (TpArrow x1 x2 x3) x4) = (norm-liftingType (LiftTpArrow  x1 (norm-liftingType (LiftTpArrow  x3 x4) )) )
  norm-liftingType (LiftArrow (LiftTpArrow x1 x2) x3) = (norm-liftingType (LiftTpArrow  x1 (norm-liftingType (LiftArrow  x2 x3) )) )
  norm-liftingType (LiftArrow (LiftArrow x1 x2) x3) = (norm-liftingType (LiftArrow  x1 (norm-liftingType (LiftArrow  x2 x3) )) )
  norm-liftingType x = x

  {-# TERMINATING #-}
  norm-leftRight : (x : leftRight) → leftRight
  norm-leftRight x = x

  {-# TERMINATING #-}
  norm-lam : (x : lam) → lam
  norm-lam x = x

  {-# TERMINATING #-}
  norm-kind : (x : kind) → kind
  norm-kind (KndArrow (KndPi x1 x2 x3 x4 x5) x6) = (norm-kind (KndPi  x1 x2 x3 x4 (norm-kind (KndArrow  x5 x6) )) )
  norm-kind (KndArrow (KndTpArrow x1 x2) x3) = (norm-kind (KndTpArrow  x1 (norm-kind (KndArrow  x2 x3) )) )
  norm-kind (KndArrow (KndArrow x1 x2) x3) = (norm-kind (KndArrow  x1 (norm-kind (KndArrow  x2 x3) )) )
  norm-kind x = x

  {-# TERMINATING #-}
  norm-imprt : (x : imprt) → imprt
  norm-imprt x = x

  {-# TERMINATING #-}
  norm-imports : (x : imports) → imports
  norm-imports x = x

  {-# TERMINATING #-}
  norm-defTermOrType : (x : defTermOrType) → defTermOrType
  norm-defTermOrType x = x

  {-# TERMINATING #-}
  norm-decl : (x : decl) → decl
  norm-decl x = x

  {-# TERMINATING #-}
  norm-cmds : (x : cmds) → cmds
  norm-cmds x = x

  {-# TERMINATING #-}
  norm-cmd : (x : cmd) → cmd
  norm-cmd x = x

  {-# TERMINATING #-}
  norm-binder : (x : binder) → binder
  norm-binder x = x

  {-# TERMINATING #-}
  norm-atype : (x : atype) → atype
  norm-atype x = x

  {-# TERMINATING #-}
  norm-aterm : (x : aterm) → aterm
  norm-aterm x = x

  {-# TERMINATING #-}
  norm-arrowtype : (x : arrowtype) → arrowtype
  norm-arrowtype x = x

  {-# TERMINATING #-}
  norm-args : (x : args) → args
  norm-args x = x

  {-# TERMINATING #-}
  norm-arg : (x : arg) → arg
  norm-arg x = x

isParseTree : ParseTreeT → 𝕃 char → string → Set
isParseTree p l s = ⊤ {- this will be ignored since we are using simply typed runs -}

ptr : ParseTreeRec
ptr = record { ParseTreeT = ParseTreeT ; isParseTree = isParseTree ; ParseTreeToString = ParseTreeToString }

