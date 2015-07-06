----------------------------------------------------------------------------------
-- Types for parse trees
----------------------------------------------------------------------------------

module cedille-types where

open import lib
open import parse-tree
evar = string
evar-bar-8 = string
kvar = string
kvar-opt-6 = string
num = string
num-plus-10 = string
numone = string
numone-range-9 = string
var = string
var-plus-7 = string
varone = string
varone-bar-3 = string
varone-bar-4 = string
varone-bar-5 = string
varone-range-1 = string
varone-range-2 = string

mutual

  data al : Set where 
    All : al
    Lambda : al

  data castDir : Set where 
    checkCast : castDir
    synthCast : castDir

  data class : Set where 
    Knd : type → kind → class
    Tp : term → type → class

  data cmd : Set where 
    DefCmd : def → cmd
    Echeck : class → evidence → evidence → cmd
    Kcheck : kind → evidence → cmd
    Normalize : term → cmd
    Print : var → cmd
    SynthTerm : var → term → evidence → cmd
    SynthType : var → type → evidence → cmd

  data cmds : Set where 
    CmdsNext : cmd → cmds → cmds
    CmdsStart : cmd → cmds

  data ctorset : Set where 
    Add : term → type → ctorset → ctorset
    Empty : ctorset

  data def : Set where 
    Edefine : var → class → evidence → evidence → def
    Kdefine : kvar → kind → evidence → def
    Tdefine : var → term → def

  data evidence : Set where 
    Beta : evidence
    Cast : evidence → castDir → evidence → evidence
    Check : evidence
    Ctor : evidence → type → evidence
    Ctora : var → evidence
    Eapp : evidence → evidence → evidence
    Eappk : evidence → type → evidence
    Eappt : evidence → term → evidence
    Earrow : evidence → evidence → evidence
    Ehole : showCtxt → evidence
    EholeNamed : showCtxt → var → evidence
    Elet : def → evidence → evidence
    Elift : var → evidence → evidence → evidence
    EliftCong : evidence → evidence
    Enu : var → var → evidence → evidence → evidence → evidence → evidence
    Eparens : evidence → evidence
    Eprint : showCtxt → evidence → evidence
    EtaAll : evidence → term → evidence
    EtaLift : num → evidence
    Evar : evar → evidence
    LamCong : evidence → evidence
    Pair : evidence → evidence → evidence
    Proj : evidence → index → evidence
    Rbeta : evidence → term → evidence → evidence
    RbetaLift : num → evidence
    Sym : evidence → evidence
    Trans : evidence → evidence → evidence
    Xi : var → opt_eclass → evidence → evidence

  data index : Set where 
    One : index
    Two : index

  data ip : Set where 
    Iota : ip
    Pi : ip

  data kind : Set where 
    KndArrow : kind → kind → kind
    KndParens : kind → kind
    KndPi : var → tk → kind → kind
    KndTpArrow : type → kind → kind
    KndVar : kvar → kind
    Star : kind

  data liftingType : Set where 
    LiftArrow : liftingType → liftingType → liftingType
    LiftParens : liftingType → liftingType
    LiftPi : var → type → liftingType → liftingType
    LiftStar : liftingType
    LiftTpArrow : type → liftingType → liftingType

  data opt_eclass : Set where 
    EclassNone : opt_eclass
    EclassSome : evidence → opt_eclass

  data showCtxt : Set where 
    showCtxtNo : showCtxt
    showCtxtYes : showCtxt

  data start : Set where 
    Cmds : cmds → start

  data term : Set where 
    App : term → term → term
    Lam : var → term → term
    Parens : term → term
    Var : var → term

  data tk : Set where 
    Tkk : kind → tk
    Tkt : type → tk

  data type : Set where 
    AbsTp1 : ip → var → type → type → type
    AbsTp2 : al → var → tk → type → type
    Lft : term → liftingType → type
    Nu : var → kind → ctorset → type → type
    TpApp : type → type → type
    TpAppt : type → term → type
    TpArrow : type → type → type
    TpParens : type → type
    TpVar : var → type
    U : type

-- embedded types:
levidence : Set
levidence = evidence
lliftingType : Set
lliftingType = liftingType
lterm : Set
lterm = term
ltype : Set
ltype = type

data ParseTreeT : Set where
  parsed-al : al → ParseTreeT
  parsed-castDir : castDir → ParseTreeT
  parsed-class : class → ParseTreeT
  parsed-cmd : cmd → ParseTreeT
  parsed-cmds : cmds → ParseTreeT
  parsed-ctorset : ctorset → ParseTreeT
  parsed-def : def → ParseTreeT
  parsed-evidence : evidence → ParseTreeT
  parsed-index : index → ParseTreeT
  parsed-ip : ip → ParseTreeT
  parsed-kind : kind → ParseTreeT
  parsed-liftingType : liftingType → ParseTreeT
  parsed-opt_eclass : opt_eclass → ParseTreeT
  parsed-showCtxt : showCtxt → ParseTreeT
  parsed-start : start → ParseTreeT
  parsed-term : term → ParseTreeT
  parsed-tk : tk → ParseTreeT
  parsed-type : type → ParseTreeT
  parsed-levidence : evidence → ParseTreeT
  parsed-lliftingType : liftingType → ParseTreeT
  parsed-lterm : term → ParseTreeT
  parsed-ltype : type → ParseTreeT
  parsed-evar : evar → ParseTreeT
  parsed-evar-bar-8 : evar-bar-8 → ParseTreeT
  parsed-kvar : kvar → ParseTreeT
  parsed-kvar-opt-6 : kvar-opt-6 → ParseTreeT
  parsed-num : num → ParseTreeT
  parsed-num-plus-10 : num-plus-10 → ParseTreeT
  parsed-numone : numone → ParseTreeT
  parsed-numone-range-9 : numone-range-9 → ParseTreeT
  parsed-var : var → ParseTreeT
  parsed-var-plus-7 : var-plus-7 → ParseTreeT
  parsed-varone : varone → ParseTreeT
  parsed-varone-bar-3 : varone-bar-3 → ParseTreeT
  parsed-varone-bar-4 : varone-bar-4 → ParseTreeT
  parsed-varone-bar-5 : varone-bar-5 → ParseTreeT
  parsed-varone-range-1 : varone-range-1 → ParseTreeT
  parsed-varone-range-2 : varone-range-2 → ParseTreeT
  parsed-anychar : ParseTreeT
  parsed-anychar-bar-11 : ParseTreeT
  parsed-anychar-bar-12 : ParseTreeT
  parsed-anychar-bar-13 : ParseTreeT
  parsed-anychar-bar-14 : ParseTreeT
  parsed-anychar-bar-15 : ParseTreeT
  parsed-anychar-bar-16 : ParseTreeT
  parsed-anychar-bar-17 : ParseTreeT
  parsed-anychar-bar-18 : ParseTreeT
  parsed-anychar-bar-19 : ParseTreeT
  parsed-anychar-bar-20 : ParseTreeT
  parsed-anychar-bar-21 : ParseTreeT
  parsed-anychar-bar-22 : ParseTreeT
  parsed-anychar-bar-23 : ParseTreeT
  parsed-anychar-bar-24 : ParseTreeT
  parsed-anychar-bar-25 : ParseTreeT
  parsed-anychar-bar-26 : ParseTreeT
  parsed-anychar-bar-27 : ParseTreeT
  parsed-anychar-bar-28 : ParseTreeT
  parsed-anychar-bar-29 : ParseTreeT
  parsed-anychar-bar-30 : ParseTreeT
  parsed-anychar-bar-31 : ParseTreeT
  parsed-anychar-bar-32 : ParseTreeT
  parsed-anychar-bar-33 : ParseTreeT
  parsed-anychar-bar-34 : ParseTreeT
  parsed-anychar-bar-35 : ParseTreeT
  parsed-anychar-bar-36 : ParseTreeT
  parsed-anychar-bar-37 : ParseTreeT
  parsed-anychar-bar-38 : ParseTreeT
  parsed-anychar-bar-39 : ParseTreeT
  parsed-anychar-bar-40 : ParseTreeT
  parsed-anychar-bar-41 : ParseTreeT
  parsed-anychar-bar-42 : ParseTreeT
  parsed-anychar-bar-43 : ParseTreeT
  parsed-anychar-bar-44 : ParseTreeT
  parsed-anychar-bar-45 : ParseTreeT
  parsed-anychar-bar-46 : ParseTreeT
  parsed-anychar-bar-47 : ParseTreeT
  parsed-anychar-bar-48 : ParseTreeT
  parsed-anychar-bar-49 : ParseTreeT
  parsed-anychar-bar-50 : ParseTreeT
  parsed-anychar-bar-51 : ParseTreeT
  parsed-anychar-bar-52 : ParseTreeT
  parsed-anychar-bar-53 : ParseTreeT
  parsed-anychar-bar-54 : ParseTreeT
  parsed-aws : ParseTreeT
  parsed-aws-bar-56 : ParseTreeT
  parsed-aws-bar-57 : ParseTreeT
  parsed-aws-bar-58 : ParseTreeT
  parsed-comment : ParseTreeT
  parsed-comment-star-55 : ParseTreeT
  parsed-ows : ParseTreeT
  parsed-ows-star-60 : ParseTreeT
  parsed-ws : ParseTreeT
  parsed-ws-plus-59 : ParseTreeT

------------------------------------------
-- Parse tree printing functions
------------------------------------------

evarToString : evar → string
evarToString x = "(evar " ^ x ^ ")"
evar-bar-8ToString : evar-bar-8 → string
evar-bar-8ToString x = "(evar-bar-8 " ^ x ^ ")"
kvarToString : kvar → string
kvarToString x = "(kvar " ^ x ^ ")"
kvar-opt-6ToString : kvar-opt-6 → string
kvar-opt-6ToString x = "(kvar-opt-6 " ^ x ^ ")"
numToString : num → string
numToString x = "(num " ^ x ^ ")"
num-plus-10ToString : num-plus-10 → string
num-plus-10ToString x = "(num-plus-10 " ^ x ^ ")"
numoneToString : numone → string
numoneToString x = "(numone " ^ x ^ ")"
numone-range-9ToString : numone-range-9 → string
numone-range-9ToString x = "(numone-range-9 " ^ x ^ ")"
varToString : var → string
varToString x = "(var " ^ x ^ ")"
var-plus-7ToString : var-plus-7 → string
var-plus-7ToString x = "(var-plus-7 " ^ x ^ ")"
varoneToString : varone → string
varoneToString x = "(varone " ^ x ^ ")"
varone-bar-3ToString : varone-bar-3 → string
varone-bar-3ToString x = "(varone-bar-3 " ^ x ^ ")"
varone-bar-4ToString : varone-bar-4 → string
varone-bar-4ToString x = "(varone-bar-4 " ^ x ^ ")"
varone-bar-5ToString : varone-bar-5 → string
varone-bar-5ToString x = "(varone-bar-5 " ^ x ^ ")"
varone-range-1ToString : varone-range-1 → string
varone-range-1ToString x = "(varone-range-1 " ^ x ^ ")"
varone-range-2ToString : varone-range-2 → string
varone-range-2ToString x = "(varone-range-2 " ^ x ^ ")"

mutual
  alToString : al → string
  alToString (All) = "All" ^ ""
  alToString (Lambda) = "Lambda" ^ ""

  castDirToString : castDir → string
  castDirToString (checkCast) = "checkCast" ^ ""
  castDirToString (synthCast) = "synthCast" ^ ""

  classToString : class → string
  classToString (Knd x0 x1) = "(Knd" ^ " " ^ (typeToString x0) ^ " " ^ (kindToString x1) ^ ")"
  classToString (Tp x0 x1) = "(Tp" ^ " " ^ (termToString x0) ^ " " ^ (typeToString x1) ^ ")"

  cmdToString : cmd → string
  cmdToString (DefCmd x0) = "(DefCmd" ^ " " ^ (defToString x0) ^ ")"
  cmdToString (Echeck x0 x1 x2) = "(Echeck" ^ " " ^ (classToString x0) ^ " " ^ (evidenceToString x1) ^ " " ^ (evidenceToString x2) ^ ")"
  cmdToString (Kcheck x0 x1) = "(Kcheck" ^ " " ^ (kindToString x0) ^ " " ^ (evidenceToString x1) ^ ")"
  cmdToString (Normalize x0) = "(Normalize" ^ " " ^ (termToString x0) ^ ")"
  cmdToString (Print x0) = "(Print" ^ " " ^ (varToString x0) ^ ")"
  cmdToString (SynthTerm x0 x1 x2) = "(SynthTerm" ^ " " ^ (varToString x0) ^ " " ^ (termToString x1) ^ " " ^ (evidenceToString x2) ^ ")"
  cmdToString (SynthType x0 x1 x2) = "(SynthType" ^ " " ^ (varToString x0) ^ " " ^ (typeToString x1) ^ " " ^ (evidenceToString x2) ^ ")"

  cmdsToString : cmds → string
  cmdsToString (CmdsNext x0 x1) = "(CmdsNext" ^ " " ^ (cmdToString x0) ^ " " ^ (cmdsToString x1) ^ ")"
  cmdsToString (CmdsStart x0) = "(CmdsStart" ^ " " ^ (cmdToString x0) ^ ")"

  ctorsetToString : ctorset → string
  ctorsetToString (Add x0 x1 x2) = "(Add" ^ " " ^ (termToString x0) ^ " " ^ (typeToString x1) ^ " " ^ (ctorsetToString x2) ^ ")"
  ctorsetToString (Empty) = "Empty" ^ ""

  defToString : def → string
  defToString (Edefine x0 x1 x2 x3) = "(Edefine" ^ " " ^ (varToString x0) ^ " " ^ (classToString x1) ^ " " ^ (evidenceToString x2) ^ " " ^ (evidenceToString x3) ^ ")"
  defToString (Kdefine x0 x1 x2) = "(Kdefine" ^ " " ^ (kvarToString x0) ^ " " ^ (kindToString x1) ^ " " ^ (evidenceToString x2) ^ ")"
  defToString (Tdefine x0 x1) = "(Tdefine" ^ " " ^ (varToString x0) ^ " " ^ (termToString x1) ^ ")"

  evidenceToString : evidence → string
  evidenceToString (Beta) = "Beta" ^ ""
  evidenceToString (Cast x0 x1 x2) = "(Cast" ^ " " ^ (evidenceToString x0) ^ " " ^ (castDirToString x1) ^ " " ^ (evidenceToString x2) ^ ")"
  evidenceToString (Check) = "Check" ^ ""
  evidenceToString (Ctor x0 x1) = "(Ctor" ^ " " ^ (evidenceToString x0) ^ " " ^ (typeToString x1) ^ ")"
  evidenceToString (Ctora x0) = "(Ctora" ^ " " ^ (varToString x0) ^ ")"
  evidenceToString (Eapp x0 x1) = "(Eapp" ^ " " ^ (evidenceToString x0) ^ " " ^ (evidenceToString x1) ^ ")"
  evidenceToString (Eappk x0 x1) = "(Eappk" ^ " " ^ (evidenceToString x0) ^ " " ^ (typeToString x1) ^ ")"
  evidenceToString (Eappt x0 x1) = "(Eappt" ^ " " ^ (evidenceToString x0) ^ " " ^ (termToString x1) ^ ")"
  evidenceToString (Earrow x0 x1) = "(Earrow" ^ " " ^ (evidenceToString x0) ^ " " ^ (evidenceToString x1) ^ ")"
  evidenceToString (Ehole x0) = "(Ehole" ^ " " ^ (showCtxtToString x0) ^ ")"
  evidenceToString (EholeNamed x0 x1) = "(EholeNamed" ^ " " ^ (showCtxtToString x0) ^ " " ^ (varToString x1) ^ ")"
  evidenceToString (Elet x0 x1) = "(Elet" ^ " " ^ (defToString x0) ^ " " ^ (evidenceToString x1) ^ ")"
  evidenceToString (Elift x0 x1 x2) = "(Elift" ^ " " ^ (varToString x0) ^ " " ^ (evidenceToString x1) ^ " " ^ (evidenceToString x2) ^ ")"
  evidenceToString (EliftCong x0) = "(EliftCong" ^ " " ^ (evidenceToString x0) ^ ")"
  evidenceToString (Enu x0 x1 x2 x3 x4 x5) = "(Enu" ^ " " ^ (varToString x0) ^ " " ^ (varToString x1) ^ " " ^ (evidenceToString x2) ^ " " ^ (evidenceToString x3) ^ " " ^ (evidenceToString x4) ^ " " ^ (evidenceToString x5) ^ ")"
  evidenceToString (Eparens x0) = "(Eparens" ^ " " ^ (evidenceToString x0) ^ ")"
  evidenceToString (Eprint x0 x1) = "(Eprint" ^ " " ^ (showCtxtToString x0) ^ " " ^ (evidenceToString x1) ^ ")"
  evidenceToString (EtaAll x0 x1) = "(EtaAll" ^ " " ^ (evidenceToString x0) ^ " " ^ (termToString x1) ^ ")"
  evidenceToString (EtaLift x0) = "(EtaLift" ^ " " ^ (numToString x0) ^ ")"
  evidenceToString (Evar x0) = "(Evar" ^ " " ^ (evarToString x0) ^ ")"
  evidenceToString (LamCong x0) = "(LamCong" ^ " " ^ (evidenceToString x0) ^ ")"
  evidenceToString (Pair x0 x1) = "(Pair" ^ " " ^ (evidenceToString x0) ^ " " ^ (evidenceToString x1) ^ ")"
  evidenceToString (Proj x0 x1) = "(Proj" ^ " " ^ (evidenceToString x0) ^ " " ^ (indexToString x1) ^ ")"
  evidenceToString (Rbeta x0 x1 x2) = "(Rbeta" ^ " " ^ (evidenceToString x0) ^ " " ^ (termToString x1) ^ " " ^ (evidenceToString x2) ^ ")"
  evidenceToString (RbetaLift x0) = "(RbetaLift" ^ " " ^ (numToString x0) ^ ")"
  evidenceToString (Sym x0) = "(Sym" ^ " " ^ (evidenceToString x0) ^ ")"
  evidenceToString (Trans x0 x1) = "(Trans" ^ " " ^ (evidenceToString x0) ^ " " ^ (evidenceToString x1) ^ ")"
  evidenceToString (Xi x0 x1 x2) = "(Xi" ^ " " ^ (varToString x0) ^ " " ^ (opt_eclassToString x1) ^ " " ^ (evidenceToString x2) ^ ")"

  indexToString : index → string
  indexToString (One) = "One" ^ ""
  indexToString (Two) = "Two" ^ ""

  ipToString : ip → string
  ipToString (Iota) = "Iota" ^ ""
  ipToString (Pi) = "Pi" ^ ""

  kindToString : kind → string
  kindToString (KndArrow x0 x1) = "(KndArrow" ^ " " ^ (kindToString x0) ^ " " ^ (kindToString x1) ^ ")"
  kindToString (KndParens x0) = "(KndParens" ^ " " ^ (kindToString x0) ^ ")"
  kindToString (KndPi x0 x1 x2) = "(KndPi" ^ " " ^ (varToString x0) ^ " " ^ (tkToString x1) ^ " " ^ (kindToString x2) ^ ")"
  kindToString (KndTpArrow x0 x1) = "(KndTpArrow" ^ " " ^ (typeToString x0) ^ " " ^ (kindToString x1) ^ ")"
  kindToString (KndVar x0) = "(KndVar" ^ " " ^ (kvarToString x0) ^ ")"
  kindToString (Star) = "Star" ^ ""

  liftingTypeToString : liftingType → string
  liftingTypeToString (LiftArrow x0 x1) = "(LiftArrow" ^ " " ^ (liftingTypeToString x0) ^ " " ^ (liftingTypeToString x1) ^ ")"
  liftingTypeToString (LiftParens x0) = "(LiftParens" ^ " " ^ (liftingTypeToString x0) ^ ")"
  liftingTypeToString (LiftPi x0 x1 x2) = "(LiftPi" ^ " " ^ (varToString x0) ^ " " ^ (typeToString x1) ^ " " ^ (liftingTypeToString x2) ^ ")"
  liftingTypeToString (LiftStar) = "LiftStar" ^ ""
  liftingTypeToString (LiftTpArrow x0 x1) = "(LiftTpArrow" ^ " " ^ (typeToString x0) ^ " " ^ (liftingTypeToString x1) ^ ")"

  opt_eclassToString : opt_eclass → string
  opt_eclassToString (EclassNone) = "EclassNone" ^ ""
  opt_eclassToString (EclassSome x0) = "(EclassSome" ^ " " ^ (evidenceToString x0) ^ ")"

  showCtxtToString : showCtxt → string
  showCtxtToString (showCtxtNo) = "showCtxtNo" ^ ""
  showCtxtToString (showCtxtYes) = "showCtxtYes" ^ ""

  startToString : start → string
  startToString (Cmds x0) = "(Cmds" ^ " " ^ (cmdsToString x0) ^ ")"

  termToString : term → string
  termToString (App x0 x1) = "(App" ^ " " ^ (termToString x0) ^ " " ^ (termToString x1) ^ ")"
  termToString (Lam x0 x1) = "(Lam" ^ " " ^ (varToString x0) ^ " " ^ (termToString x1) ^ ")"
  termToString (Parens x0) = "(Parens" ^ " " ^ (termToString x0) ^ ")"
  termToString (Var x0) = "(Var" ^ " " ^ (varToString x0) ^ ")"

  tkToString : tk → string
  tkToString (Tkk x0) = "(Tkk" ^ " " ^ (kindToString x0) ^ ")"
  tkToString (Tkt x0) = "(Tkt" ^ " " ^ (typeToString x0) ^ ")"

  typeToString : type → string
  typeToString (AbsTp1 x0 x1 x2 x3) = "(AbsTp1" ^ " " ^ (ipToString x0) ^ " " ^ (varToString x1) ^ " " ^ (typeToString x2) ^ " " ^ (typeToString x3) ^ ")"
  typeToString (AbsTp2 x0 x1 x2 x3) = "(AbsTp2" ^ " " ^ (alToString x0) ^ " " ^ (varToString x1) ^ " " ^ (tkToString x2) ^ " " ^ (typeToString x3) ^ ")"
  typeToString (Lft x0 x1) = "(Lft" ^ " " ^ (termToString x0) ^ " " ^ (liftingTypeToString x1) ^ ")"
  typeToString (Nu x0 x1 x2 x3) = "(Nu" ^ " " ^ (varToString x0) ^ " " ^ (kindToString x1) ^ " " ^ (ctorsetToString x2) ^ " " ^ (typeToString x3) ^ ")"
  typeToString (TpApp x0 x1) = "(TpApp" ^ " " ^ (typeToString x0) ^ " " ^ (typeToString x1) ^ ")"
  typeToString (TpAppt x0 x1) = "(TpAppt" ^ " " ^ (typeToString x0) ^ " " ^ (termToString x1) ^ ")"
  typeToString (TpArrow x0 x1) = "(TpArrow" ^ " " ^ (typeToString x0) ^ " " ^ (typeToString x1) ^ ")"
  typeToString (TpParens x0) = "(TpParens" ^ " " ^ (typeToString x0) ^ ")"
  typeToString (TpVar x0) = "(TpVar" ^ " " ^ (varToString x0) ^ ")"
  typeToString (U) = "U" ^ ""

ParseTreeToString : ParseTreeT → string
ParseTreeToString (parsed-al t) = alToString t
ParseTreeToString (parsed-castDir t) = castDirToString t
ParseTreeToString (parsed-class t) = classToString t
ParseTreeToString (parsed-cmd t) = cmdToString t
ParseTreeToString (parsed-cmds t) = cmdsToString t
ParseTreeToString (parsed-ctorset t) = ctorsetToString t
ParseTreeToString (parsed-def t) = defToString t
ParseTreeToString (parsed-evidence t) = evidenceToString t
ParseTreeToString (parsed-index t) = indexToString t
ParseTreeToString (parsed-ip t) = ipToString t
ParseTreeToString (parsed-kind t) = kindToString t
ParseTreeToString (parsed-liftingType t) = liftingTypeToString t
ParseTreeToString (parsed-opt_eclass t) = opt_eclassToString t
ParseTreeToString (parsed-showCtxt t) = showCtxtToString t
ParseTreeToString (parsed-start t) = startToString t
ParseTreeToString (parsed-term t) = termToString t
ParseTreeToString (parsed-tk t) = tkToString t
ParseTreeToString (parsed-type t) = typeToString t
ParseTreeToString (parsed-levidence t) = evidenceToString t
ParseTreeToString (parsed-lliftingType t) = liftingTypeToString t
ParseTreeToString (parsed-lterm t) = termToString t
ParseTreeToString (parsed-ltype t) = typeToString t
ParseTreeToString (parsed-evar t) = evarToString t
ParseTreeToString (parsed-evar-bar-8 t) = evar-bar-8ToString t
ParseTreeToString (parsed-kvar t) = kvarToString t
ParseTreeToString (parsed-kvar-opt-6 t) = kvar-opt-6ToString t
ParseTreeToString (parsed-num t) = numToString t
ParseTreeToString (parsed-num-plus-10 t) = num-plus-10ToString t
ParseTreeToString (parsed-numone t) = numoneToString t
ParseTreeToString (parsed-numone-range-9 t) = numone-range-9ToString t
ParseTreeToString (parsed-var t) = varToString t
ParseTreeToString (parsed-var-plus-7 t) = var-plus-7ToString t
ParseTreeToString (parsed-varone t) = varoneToString t
ParseTreeToString (parsed-varone-bar-3 t) = varone-bar-3ToString t
ParseTreeToString (parsed-varone-bar-4 t) = varone-bar-4ToString t
ParseTreeToString (parsed-varone-bar-5 t) = varone-bar-5ToString t
ParseTreeToString (parsed-varone-range-1 t) = varone-range-1ToString t
ParseTreeToString (parsed-varone-range-2 t) = varone-range-2ToString t
ParseTreeToString parsed-anychar = "[anychar]"
ParseTreeToString parsed-anychar-bar-11 = "[anychar-bar-11]"
ParseTreeToString parsed-anychar-bar-12 = "[anychar-bar-12]"
ParseTreeToString parsed-anychar-bar-13 = "[anychar-bar-13]"
ParseTreeToString parsed-anychar-bar-14 = "[anychar-bar-14]"
ParseTreeToString parsed-anychar-bar-15 = "[anychar-bar-15]"
ParseTreeToString parsed-anychar-bar-16 = "[anychar-bar-16]"
ParseTreeToString parsed-anychar-bar-17 = "[anychar-bar-17]"
ParseTreeToString parsed-anychar-bar-18 = "[anychar-bar-18]"
ParseTreeToString parsed-anychar-bar-19 = "[anychar-bar-19]"
ParseTreeToString parsed-anychar-bar-20 = "[anychar-bar-20]"
ParseTreeToString parsed-anychar-bar-21 = "[anychar-bar-21]"
ParseTreeToString parsed-anychar-bar-22 = "[anychar-bar-22]"
ParseTreeToString parsed-anychar-bar-23 = "[anychar-bar-23]"
ParseTreeToString parsed-anychar-bar-24 = "[anychar-bar-24]"
ParseTreeToString parsed-anychar-bar-25 = "[anychar-bar-25]"
ParseTreeToString parsed-anychar-bar-26 = "[anychar-bar-26]"
ParseTreeToString parsed-anychar-bar-27 = "[anychar-bar-27]"
ParseTreeToString parsed-anychar-bar-28 = "[anychar-bar-28]"
ParseTreeToString parsed-anychar-bar-29 = "[anychar-bar-29]"
ParseTreeToString parsed-anychar-bar-30 = "[anychar-bar-30]"
ParseTreeToString parsed-anychar-bar-31 = "[anychar-bar-31]"
ParseTreeToString parsed-anychar-bar-32 = "[anychar-bar-32]"
ParseTreeToString parsed-anychar-bar-33 = "[anychar-bar-33]"
ParseTreeToString parsed-anychar-bar-34 = "[anychar-bar-34]"
ParseTreeToString parsed-anychar-bar-35 = "[anychar-bar-35]"
ParseTreeToString parsed-anychar-bar-36 = "[anychar-bar-36]"
ParseTreeToString parsed-anychar-bar-37 = "[anychar-bar-37]"
ParseTreeToString parsed-anychar-bar-38 = "[anychar-bar-38]"
ParseTreeToString parsed-anychar-bar-39 = "[anychar-bar-39]"
ParseTreeToString parsed-anychar-bar-40 = "[anychar-bar-40]"
ParseTreeToString parsed-anychar-bar-41 = "[anychar-bar-41]"
ParseTreeToString parsed-anychar-bar-42 = "[anychar-bar-42]"
ParseTreeToString parsed-anychar-bar-43 = "[anychar-bar-43]"
ParseTreeToString parsed-anychar-bar-44 = "[anychar-bar-44]"
ParseTreeToString parsed-anychar-bar-45 = "[anychar-bar-45]"
ParseTreeToString parsed-anychar-bar-46 = "[anychar-bar-46]"
ParseTreeToString parsed-anychar-bar-47 = "[anychar-bar-47]"
ParseTreeToString parsed-anychar-bar-48 = "[anychar-bar-48]"
ParseTreeToString parsed-anychar-bar-49 = "[anychar-bar-49]"
ParseTreeToString parsed-anychar-bar-50 = "[anychar-bar-50]"
ParseTreeToString parsed-anychar-bar-51 = "[anychar-bar-51]"
ParseTreeToString parsed-anychar-bar-52 = "[anychar-bar-52]"
ParseTreeToString parsed-anychar-bar-53 = "[anychar-bar-53]"
ParseTreeToString parsed-anychar-bar-54 = "[anychar-bar-54]"
ParseTreeToString parsed-aws = "[aws]"
ParseTreeToString parsed-aws-bar-56 = "[aws-bar-56]"
ParseTreeToString parsed-aws-bar-57 = "[aws-bar-57]"
ParseTreeToString parsed-aws-bar-58 = "[aws-bar-58]"
ParseTreeToString parsed-comment = "[comment]"
ParseTreeToString parsed-comment-star-55 = "[comment-star-55]"
ParseTreeToString parsed-ows = "[ows]"
ParseTreeToString parsed-ows-star-60 = "[ows-star-60]"
ParseTreeToString parsed-ws = "[ws]"
ParseTreeToString parsed-ws-plus-59 = "[ws-plus-59]"

------------------------------------------
-- Reorganizing rules
------------------------------------------

mutual

  {-# NO_TERMINATION_CHECK #-}
  norm-type : (x : type) → type
  norm-type (TpAppt x1 (App x2 x3)) = (norm-type (TpAppt  (norm-type (TpAppt  x1 x2) ) x3) )
  norm-type (TpApp x1 (TpAppt x2 x3)) = (norm-type (TpAppt  (norm-type (TpApp  x1 x2) ) x3) )
  norm-type (TpApp x1 (TpApp x2 x3)) = (norm-type (TpApp  (norm-type (TpApp  x1 x2) ) x3) )
  norm-type x = x

  {-# NO_TERMINATION_CHECK #-}
  norm-tk : (x : tk) → tk
  norm-tk x = x

  {-# NO_TERMINATION_CHECK #-}
  norm-term : (x : term) → term
  norm-term (App x1 (App x2 x3)) = (norm-term (App  (norm-term (App  x1 x2) ) x3) )
  norm-term x = x

  {-# NO_TERMINATION_CHECK #-}
  norm-start : (x : start) → start
  norm-start x = x

  {-# NO_TERMINATION_CHECK #-}
  norm-showCtxt : (x : showCtxt) → showCtxt
  norm-showCtxt x = x

  {-# NO_TERMINATION_CHECK #-}
  norm-opt_eclass : (x : opt_eclass) → opt_eclass
  norm-opt_eclass x = x

  {-# NO_TERMINATION_CHECK #-}
  norm-ltype : (x : ltype) → ltype
  norm-ltype x = x

  {-# NO_TERMINATION_CHECK #-}
  norm-lterm : (x : lterm) → lterm
  norm-lterm x = x

  {-# NO_TERMINATION_CHECK #-}
  norm-lliftingType : (x : lliftingType) → lliftingType
  norm-lliftingType x = x

  {-# NO_TERMINATION_CHECK #-}
  norm-liftingType : (x : liftingType) → liftingType
  norm-liftingType (LiftArrow (LiftPi x1 x2 x3) x4) = (norm-liftingType (LiftPi  x1 x2 (norm-liftingType (LiftArrow  x3 x4) )) )
  norm-liftingType (LiftTpArrow (TpArrow x1 x2) x3) = (norm-liftingType (LiftTpArrow  x1 (norm-liftingType (LiftTpArrow  x2 x3) )) )
  norm-liftingType (LiftArrow (LiftTpArrow x1 x2) x3) = (norm-liftingType (LiftTpArrow  x1 (norm-liftingType (LiftArrow  x2 x3) )) )
  norm-liftingType (LiftArrow (LiftArrow x1 x2) x3) = (norm-liftingType (LiftArrow  x1 (norm-liftingType (LiftArrow  x2 x3) )) )
  norm-liftingType x = x

  {-# NO_TERMINATION_CHECK #-}
  norm-levidence : (x : levidence) → levidence
  norm-levidence x = x

  {-# NO_TERMINATION_CHECK #-}
  norm-kind : (x : kind) → kind
  norm-kind (KndArrow (KndPi x1 x2 x3) x4) = (norm-kind (KndPi  x1 x2 (norm-kind (KndArrow  x3 x4) )) )
  norm-kind (KndArrow (KndTpArrow x1 x2) x3) = (norm-kind (KndTpArrow  x1 (norm-kind (KndArrow  x2 x3) )) )
  norm-kind (KndArrow (KndArrow x1 x2) x3) = (norm-kind (KndArrow  x1 (norm-kind (KndArrow  x2 x3) )) )
  norm-kind x = x

  {-# NO_TERMINATION_CHECK #-}
  norm-ip : (x : ip) → ip
  norm-ip x = x

  {-# NO_TERMINATION_CHECK #-}
  norm-index : (x : index) → index
  norm-index x = x

  {-# NO_TERMINATION_CHECK #-}
  norm-evidence : (x : evidence) → evidence
  norm-evidence (Proj (Trans x1 x2) x3) = (norm-evidence (Trans  x1 (norm-evidence (Proj  x2 x3) )) )
  norm-evidence (Proj (Sym x1) x2) = (norm-evidence (Sym  (norm-evidence (Proj  x1 x2) )) )
  norm-evidence (Sym (Earrow x1 x2)) = (norm-evidence (Earrow  (norm-evidence (Sym  x1) ) x2) )
  norm-evidence (Trans x1 (Earrow x2 x3)) = (norm-evidence (Earrow  (norm-evidence (Trans  x1 x2) ) x3) )
  norm-evidence (Trans (Earrow x1 x2) x3) = (norm-evidence (Earrow  x1 (norm-evidence (Trans  x2 x3) )) )
  norm-evidence (Eapp x1 (Trans x2 x3)) = (norm-evidence (Trans  (norm-evidence (Eapp  x1 x2) ) x3) )
  norm-evidence (Eapp (Trans x1 x2) x3) = (norm-evidence (Trans  x1 (norm-evidence (Eapp  x2 x3) )) )
  norm-evidence (Sym (Eapp x1 x2)) = (norm-evidence (Eapp  (norm-evidence (Sym  x1) ) x2) )
  norm-evidence (Sym (Trans x1 x2)) = (norm-evidence (Trans  (norm-evidence (Sym  x1) ) x2) )
  norm-evidence (Trans (Trans x1 x2) x3) = (norm-evidence (Trans  x1 (norm-evidence (Trans  x2 x3) )) )
  norm-evidence (Proj (Eapp x1 x2) x3) = (norm-evidence (Eapp  x1 (norm-evidence (Proj  x2 x3) )) )
  norm-evidence (Proj (Earrow x1 x2) x3) = (norm-evidence (Earrow  x1 (norm-evidence (Proj  x2 x3) )) )
  norm-evidence (Eapp x1 (Earrow x2 x3)) = (norm-evidence (Earrow  (norm-evidence (Eapp  x1 x2) ) x3) )
  norm-evidence (Eapp (Earrow x1 x2) x3) = (norm-evidence (Earrow  x1 (norm-evidence (Eapp  x2 x3) )) )
  norm-evidence (Earrow (Earrow x1 x2) x3) = (norm-evidence (Earrow  x1 (norm-evidence (Earrow  x2 x3) )) )
  norm-evidence (Eapp x1 (Eapp x2 x3)) = (norm-evidence (Eapp  (norm-evidence (Eapp  x1 x2) ) x3) )
  norm-evidence x = x

  {-# NO_TERMINATION_CHECK #-}
  norm-def : (x : def) → def
  norm-def x = x

  {-# NO_TERMINATION_CHECK #-}
  norm-ctorset : (x : ctorset) → ctorset
  norm-ctorset x = x

  {-# NO_TERMINATION_CHECK #-}
  norm-cmds : (x : cmds) → cmds
  norm-cmds x = x

  {-# NO_TERMINATION_CHECK #-}
  norm-cmd : (x : cmd) → cmd
  norm-cmd x = x

  {-# NO_TERMINATION_CHECK #-}
  norm-class : (x : class) → class
  norm-class x = x

  {-# NO_TERMINATION_CHECK #-}
  norm-castDir : (x : castDir) → castDir
  norm-castDir x = x

  {-# NO_TERMINATION_CHECK #-}
  norm-al : (x : al) → al
  norm-al x = x

isParseTree : ParseTreeT → 𝕃 char → string → Set
isParseTree p l s = ⊤ {- this will be ignored since we are using simply typed runs -}

ptr : ParseTreeRec
ptr = record { ParseTreeT = ParseTreeT ; isParseTree = isParseTree ; ParseTreeToString = ParseTreeToString }

