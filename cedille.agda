module cedille where

open import lib

open import cedille-types public
----------------------------------------------------------------------------------
-- Run-rewriting rules
----------------------------------------------------------------------------------

data gratr2-nt : Set where
  _ws-plus-45 : gratr2-nt
  _ws : gratr2-nt
  _var-star-8 : gratr2-nt
  _var-bar-7 : gratr2-nt
  _var : gratr2-nt
  _udefsne : gratr2-nt
  _udefs : gratr2-nt
  _udef : gratr2-nt
  _type : gratr2-nt
  _tk : gratr2-nt
  _term : gratr2-nt
  _start : gratr2-nt
  _posinfo : gratr2-nt
  _ows-star-46 : gratr2-nt
  _ows : gratr2-nt
  _optClass : gratr2-nt
  _numpunct-range-4 : gratr2-nt
  _numpunct-bar-6 : gratr2-nt
  _numpunct-bar-5 : gratr2-nt
  _numpunct : gratr2-nt
  _maybeVarEq : gratr2-nt
  _maybeKvarEq : gratr2-nt
  _maybeErased : gratr2-nt
  _ltype : gratr2-nt
  _lterm : gratr2-nt
  _lliftingType : gratr2-nt
  _liftingType : gratr2-nt
  _lam : gratr2-nt
  _kvar-star-10 : gratr2-nt
  _kvar-bar-9 : gratr2-nt
  _kvar : gratr2-nt
  _kind : gratr2-nt
  _indices : gratr2-nt
  _decls : gratr2-nt
  _decl : gratr2-nt
  _ctordeclsne : gratr2-nt
  _ctordecls : gratr2-nt
  _ctordecl : gratr2-nt
  _comment-star-41 : gratr2-nt
  _comment : gratr2-nt
  _cmds : gratr2-nt
  _cmd : gratr2-nt
  _binder : gratr2-nt
  _aws-bar-44 : gratr2-nt
  _aws-bar-43 : gratr2-nt
  _aws-bar-42 : gratr2-nt
  _aws : gratr2-nt
  _anychar-bar-40 : gratr2-nt
  _anychar-bar-39 : gratr2-nt
  _anychar-bar-38 : gratr2-nt
  _anychar-bar-37 : gratr2-nt
  _anychar-bar-36 : gratr2-nt
  _anychar-bar-35 : gratr2-nt
  _anychar-bar-34 : gratr2-nt
  _anychar-bar-33 : gratr2-nt
  _anychar-bar-32 : gratr2-nt
  _anychar-bar-31 : gratr2-nt
  _anychar-bar-30 : gratr2-nt
  _anychar-bar-29 : gratr2-nt
  _anychar-bar-28 : gratr2-nt
  _anychar-bar-27 : gratr2-nt
  _anychar-bar-26 : gratr2-nt
  _anychar-bar-25 : gratr2-nt
  _anychar-bar-24 : gratr2-nt
  _anychar-bar-23 : gratr2-nt
  _anychar-bar-22 : gratr2-nt
  _anychar-bar-21 : gratr2-nt
  _anychar-bar-20 : gratr2-nt
  _anychar-bar-19 : gratr2-nt
  _anychar-bar-18 : gratr2-nt
  _anychar-bar-17 : gratr2-nt
  _anychar-bar-16 : gratr2-nt
  _anychar-bar-15 : gratr2-nt
  _anychar-bar-14 : gratr2-nt
  _anychar-bar-13 : gratr2-nt
  _anychar-bar-12 : gratr2-nt
  _anychar-bar-11 : gratr2-nt
  _anychar : gratr2-nt
  _alpha-range-2 : gratr2-nt
  _alpha-range-1 : gratr2-nt
  _alpha-bar-3 : gratr2-nt
  _alpha : gratr2-nt


gratr2-nt-eq : gratr2-nt → gratr2-nt → 𝔹
gratr2-nt-eq  _ws-plus-45 _ws-plus-45 = tt
gratr2-nt-eq  _ws _ws = tt
gratr2-nt-eq  _var-star-8 _var-star-8 = tt
gratr2-nt-eq  _var-bar-7 _var-bar-7 = tt
gratr2-nt-eq  _var _var = tt
gratr2-nt-eq  _udefsne _udefsne = tt
gratr2-nt-eq  _udefs _udefs = tt
gratr2-nt-eq  _udef _udef = tt
gratr2-nt-eq  _type _type = tt
gratr2-nt-eq  _tk _tk = tt
gratr2-nt-eq  _term _term = tt
gratr2-nt-eq  _start _start = tt
gratr2-nt-eq  _posinfo _posinfo = tt
gratr2-nt-eq  _ows-star-46 _ows-star-46 = tt
gratr2-nt-eq  _ows _ows = tt
gratr2-nt-eq  _optClass _optClass = tt
gratr2-nt-eq  _numpunct-range-4 _numpunct-range-4 = tt
gratr2-nt-eq  _numpunct-bar-6 _numpunct-bar-6 = tt
gratr2-nt-eq  _numpunct-bar-5 _numpunct-bar-5 = tt
gratr2-nt-eq  _numpunct _numpunct = tt
gratr2-nt-eq  _maybeVarEq _maybeVarEq = tt
gratr2-nt-eq  _maybeKvarEq _maybeKvarEq = tt
gratr2-nt-eq  _maybeErased _maybeErased = tt
gratr2-nt-eq  _ltype _ltype = tt
gratr2-nt-eq  _lterm _lterm = tt
gratr2-nt-eq  _lliftingType _lliftingType = tt
gratr2-nt-eq  _liftingType _liftingType = tt
gratr2-nt-eq  _lam _lam = tt
gratr2-nt-eq  _kvar-star-10 _kvar-star-10 = tt
gratr2-nt-eq  _kvar-bar-9 _kvar-bar-9 = tt
gratr2-nt-eq  _kvar _kvar = tt
gratr2-nt-eq  _kind _kind = tt
gratr2-nt-eq  _indices _indices = tt
gratr2-nt-eq  _decls _decls = tt
gratr2-nt-eq  _decl _decl = tt
gratr2-nt-eq  _ctordeclsne _ctordeclsne = tt
gratr2-nt-eq  _ctordecls _ctordecls = tt
gratr2-nt-eq  _ctordecl _ctordecl = tt
gratr2-nt-eq  _comment-star-41 _comment-star-41 = tt
gratr2-nt-eq  _comment _comment = tt
gratr2-nt-eq  _cmds _cmds = tt
gratr2-nt-eq  _cmd _cmd = tt
gratr2-nt-eq  _binder _binder = tt
gratr2-nt-eq  _aws-bar-44 _aws-bar-44 = tt
gratr2-nt-eq  _aws-bar-43 _aws-bar-43 = tt
gratr2-nt-eq  _aws-bar-42 _aws-bar-42 = tt
gratr2-nt-eq  _aws _aws = tt
gratr2-nt-eq  _anychar-bar-40 _anychar-bar-40 = tt
gratr2-nt-eq  _anychar-bar-39 _anychar-bar-39 = tt
gratr2-nt-eq  _anychar-bar-38 _anychar-bar-38 = tt
gratr2-nt-eq  _anychar-bar-37 _anychar-bar-37 = tt
gratr2-nt-eq  _anychar-bar-36 _anychar-bar-36 = tt
gratr2-nt-eq  _anychar-bar-35 _anychar-bar-35 = tt
gratr2-nt-eq  _anychar-bar-34 _anychar-bar-34 = tt
gratr2-nt-eq  _anychar-bar-33 _anychar-bar-33 = tt
gratr2-nt-eq  _anychar-bar-32 _anychar-bar-32 = tt
gratr2-nt-eq  _anychar-bar-31 _anychar-bar-31 = tt
gratr2-nt-eq  _anychar-bar-30 _anychar-bar-30 = tt
gratr2-nt-eq  _anychar-bar-29 _anychar-bar-29 = tt
gratr2-nt-eq  _anychar-bar-28 _anychar-bar-28 = tt
gratr2-nt-eq  _anychar-bar-27 _anychar-bar-27 = tt
gratr2-nt-eq  _anychar-bar-26 _anychar-bar-26 = tt
gratr2-nt-eq  _anychar-bar-25 _anychar-bar-25 = tt
gratr2-nt-eq  _anychar-bar-24 _anychar-bar-24 = tt
gratr2-nt-eq  _anychar-bar-23 _anychar-bar-23 = tt
gratr2-nt-eq  _anychar-bar-22 _anychar-bar-22 = tt
gratr2-nt-eq  _anychar-bar-21 _anychar-bar-21 = tt
gratr2-nt-eq  _anychar-bar-20 _anychar-bar-20 = tt
gratr2-nt-eq  _anychar-bar-19 _anychar-bar-19 = tt
gratr2-nt-eq  _anychar-bar-18 _anychar-bar-18 = tt
gratr2-nt-eq  _anychar-bar-17 _anychar-bar-17 = tt
gratr2-nt-eq  _anychar-bar-16 _anychar-bar-16 = tt
gratr2-nt-eq  _anychar-bar-15 _anychar-bar-15 = tt
gratr2-nt-eq  _anychar-bar-14 _anychar-bar-14 = tt
gratr2-nt-eq  _anychar-bar-13 _anychar-bar-13 = tt
gratr2-nt-eq  _anychar-bar-12 _anychar-bar-12 = tt
gratr2-nt-eq  _anychar-bar-11 _anychar-bar-11 = tt
gratr2-nt-eq  _anychar _anychar = tt
gratr2-nt-eq  _alpha-range-2 _alpha-range-2 = tt
gratr2-nt-eq  _alpha-range-1 _alpha-range-1 = tt
gratr2-nt-eq  _alpha-bar-3 _alpha-bar-3 = tt
gratr2-nt-eq  _alpha _alpha = tt
gratr2-nt-eq _ _ = ff


open import rtn gratr2-nt


cedille-start : gratr2-nt → 𝕃 gratr2-rule
cedille-start _ws-plus-45 = (just "P152" , nothing , just _ws-plus-45 , inj₁ _aws :: inj₁ _ws-plus-45 :: []) :: (just "P151" , nothing , just _ws-plus-45 , inj₁ _aws :: []) :: []
cedille-start _ws = (just "P153" , nothing , just _ws , inj₁ _ws-plus-45 :: []) :: []
cedille-start _var-star-8 = (just "P73" , nothing , just _var-star-8 , inj₁ _var-bar-7 :: inj₁ _var-star-8 :: []) :: (just "P72" , nothing , just _var-star-8 , []) :: []
cedille-start _var-bar-7 = (just "P71" , nothing , just _var-bar-7 , inj₁ _numpunct :: []) :: (just "P70" , nothing , just _var-bar-7 , inj₁ _alpha :: []) :: []
cedille-start _var = (just "P74" , nothing , just _var , inj₁ _alpha :: inj₁ _var-star-8 :: []) :: []
cedille-start _udefsne = (just "UdefsneStart" , nothing , just _udefsne , inj₁ _ows :: inj₁ _udef :: []) :: (just "UdefsneNext" , nothing , just _udefsne , inj₁ _ows :: inj₁ _udef :: inj₁ _ows :: inj₂ ',' :: inj₁ _udefsne :: []) :: []
cedille-start _udefs = (just "Udefsne" , nothing , just _udefs , inj₁ _udefsne :: []) :: (just "Udefse" , nothing , just _udefs , []) :: []
cedille-start _udef = (just "Udef" , just "Udef_end" , just _udef , inj₁ _var :: inj₁ _ows :: inj₂ '=' :: inj₁ _ows :: inj₁ _term :: []) :: []
cedille-start _type = (just "embed" , just "embed_end" , just _type , inj₁ _ltype :: []) :: (just "TpArrow" , nothing , just _type , inj₁ _ltype :: inj₁ _ows :: inj₂ '→' :: inj₁ _ows :: inj₁ _type :: []) :: (just "Abs" , nothing , just _type , inj₁ _posinfo :: inj₁ _binder :: inj₁ _ows :: inj₁ _var :: inj₁ _ows :: inj₂ ':' :: inj₁ _ows :: inj₁ _tk :: inj₁ _ows :: inj₂ '.' :: inj₁ _ows :: inj₁ _type :: []) :: []
cedille-start _tk = (just "Tkt" , nothing , just _tk , inj₁ _type :: []) :: (just "Tkk" , just "Tkk_end" , just _tk , inj₁ _kind :: []) :: []
cedille-start _term = (just "embed" , nothing , just _term , inj₁ _lterm :: []) :: (just "Lam" , nothing , just _term , inj₁ _posinfo :: inj₁ _lam :: inj₁ _ows :: inj₁ _var :: inj₁ _optClass :: inj₁ _ows :: inj₂ '.' :: inj₁ _ows :: inj₁ _term :: []) :: []
cedille-start _start = (just "Cmds" , nothing , just _start , inj₁ _ows :: inj₁ _cmds :: inj₁ _ows :: []) :: []
cedille-start _posinfo = (just "Posinfo" , nothing , just _posinfo , []) :: []
cedille-start _ows-star-46 = (just "P155" , nothing , just _ows-star-46 , inj₁ _aws :: inj₁ _ows-star-46 :: []) :: (just "P154" , nothing , just _ows-star-46 , []) :: []
cedille-start _ows = (just "P156" , nothing , just _ows , inj₁ _ows-star-46 :: []) :: []
cedille-start _optClass = (just "SomeClass" , nothing , just _optClass , inj₂ ':' :: inj₁ _ows :: inj₁ _tk :: []) :: (just "NoClass" , nothing , just _optClass , []) :: []
cedille-start _numpunct-range-4 = (just "P64" , nothing , just _numpunct-range-4 , inj₂ '9' :: []) :: (just "P63" , nothing , just _numpunct-range-4 , inj₂ '8' :: []) :: (just "P62" , nothing , just _numpunct-range-4 , inj₂ '7' :: []) :: (just "P61" , nothing , just _numpunct-range-4 , inj₂ '6' :: []) :: (just "P60" , nothing , just _numpunct-range-4 , inj₂ '5' :: []) :: (just "P59" , nothing , just _numpunct-range-4 , inj₂ '4' :: []) :: (just "P58" , nothing , just _numpunct-range-4 , inj₂ '3' :: []) :: (just "P57" , nothing , just _numpunct-range-4 , inj₂ '2' :: []) :: (just "P56" , nothing , just _numpunct-range-4 , inj₂ '1' :: []) :: (just "P55" , nothing , just _numpunct-range-4 , inj₂ '0' :: []) :: []
cedille-start _numpunct-bar-6 = (just "P68" , nothing , just _numpunct-bar-6 , inj₁ _numpunct-bar-5 :: []) :: (just "P67" , nothing , just _numpunct-bar-6 , inj₁ _numpunct-range-4 :: []) :: []
cedille-start _numpunct-bar-5 = (just "P66" , nothing , just _numpunct-bar-5 , inj₂ '-' :: []) :: (just "P65" , nothing , just _numpunct-bar-5 , inj₂ '\'' :: []) :: []
cedille-start _numpunct = (just "P69" , nothing , just _numpunct , inj₁ _numpunct-bar-6 :: []) :: []
cedille-start _maybeVarEq = (just "VarEq" , nothing , just _maybeVarEq , inj₁ _var :: inj₁ _ows :: inj₂ '=' :: inj₁ _ows :: []) :: (just "NoVarEq" , nothing , just _maybeVarEq , []) :: []
cedille-start _maybeKvarEq = (just "NoKvarEq" , nothing , just _maybeKvarEq , []) :: (just "KvarEq" , nothing , just _maybeKvarEq , inj₁ _kvar :: inj₁ _ows :: inj₂ '=' :: inj₁ _ows :: []) :: []
cedille-start _maybeErased = (just "NotErased" , nothing , just _maybeErased , []) :: (just "Erased" , nothing , just _maybeErased , inj₂ '-' :: inj₁ _ows :: []) :: []
cedille-start _ltype = (just "TpVar" , nothing , just _ltype , inj₁ _posinfo :: inj₁ _var :: []) :: (just "TpParens" , nothing , just _ltype , inj₁ _posinfo :: inj₂ '(' :: inj₁ _ows :: inj₁ _type :: inj₁ _ows :: inj₂ ')' :: inj₁ _posinfo :: []) :: (just "TpEq" , nothing , just _ltype , inj₁ _lterm :: inj₁ _ows :: inj₂ '≃' :: inj₁ _ows :: inj₁ _lterm :: []) :: (just "Lft" , nothing , just _ltype , inj₁ _posinfo :: inj₂ '↑' :: inj₁ _ows :: inj₁ _term :: inj₁ _ows :: inj₂ ':' :: inj₁ _ows :: inj₁ _lliftingType :: []) :: []
cedille-start _lterm = (just "Var" , nothing , just _lterm , inj₁ _posinfo :: inj₁ _var :: []) :: (just "Parens" , nothing , just _lterm , inj₁ _posinfo :: inj₂ '(' :: inj₁ _ows :: inj₁ _term :: inj₁ _ows :: inj₂ ')' :: inj₁ _posinfo :: []) :: (just "Hole" , nothing , just _lterm , inj₁ _posinfo :: inj₂ '●' :: []) :: []
cedille-start _lliftingType = (just "LiftParens" , nothing , just _lliftingType , inj₁ _posinfo :: inj₂ '(' :: inj₁ _ows :: inj₁ _liftingType :: inj₁ _ows :: inj₂ ')' :: inj₁ _posinfo :: []) :: []
cedille-start _liftingType = (just "embed" , nothing , just _liftingType , inj₁ _lliftingType :: []) :: (just "LiftTpArrow" , nothing , just _liftingType , inj₁ _type :: inj₁ _ows :: inj₂ '→' :: inj₁ _ows :: inj₁ _liftingType :: []) :: (just "LiftStar" , nothing , just _liftingType , inj₁ _posinfo :: inj₂ '☆' :: []) :: (just "LiftPi" , nothing , just _liftingType , inj₁ _posinfo :: inj₂ 'Π' :: inj₁ _ows :: inj₁ _var :: inj₁ _ows :: inj₂ ':' :: inj₁ _ows :: inj₁ _type :: inj₁ _ows :: inj₂ '.' :: inj₁ _ows :: inj₁ _liftingType :: []) :: []
cedille-start _lam = (just "KeptLambda" , nothing , just _lam , inj₂ 'λ' :: []) :: (just "ErasedLambda" , nothing , just _lam , inj₂ 'Λ' :: []) :: []
cedille-start _kvar-star-10 = (just "P78" , nothing , just _kvar-star-10 , inj₁ _kvar-bar-9 :: inj₁ _kvar-star-10 :: []) :: (just "P77" , nothing , just _kvar-star-10 , []) :: []
cedille-start _kvar-bar-9 = (just "P76" , nothing , just _kvar-bar-9 , inj₁ _numpunct :: []) :: (just "P75" , nothing , just _kvar-bar-9 , inj₁ _alpha :: []) :: []
cedille-start _kvar = (just "P79" , nothing , just _kvar , inj₂ '𝒌' :: inj₁ _kvar-star-10 :: []) :: []
cedille-start _kind = (just "Star" , nothing , just _kind , inj₁ _posinfo :: inj₂ '★' :: []) :: (just "KndVar" , nothing , just _kind , inj₁ _posinfo :: inj₁ _kvar :: []) :: (just "KndTpArrow" , nothing , just _kind , inj₁ _ltype :: inj₁ _ows :: inj₂ '→' :: inj₁ _ows :: inj₁ _kind :: []) :: (just "KndPi" , nothing , just _kind , inj₁ _posinfo :: inj₂ 'Π' :: inj₁ _ows :: inj₁ _var :: inj₁ _ows :: inj₂ ':' :: inj₁ _ows :: inj₁ _tk :: inj₁ _ows :: inj₂ '.' :: inj₁ _ows :: inj₁ _kind :: []) :: (just "KndParens" , nothing , just _kind , inj₁ _posinfo :: inj₂ '(' :: inj₁ _ows :: inj₁ _kind :: inj₁ _ows :: inj₂ ')' :: inj₁ _posinfo :: []) :: []
cedille-start _indices = (just "Indicesne" , nothing , just _indices , inj₁ _ows :: inj₂ ':' :: inj₁ _decls :: []) :: (just "Indicese" , nothing , just _indices , inj₁ _posinfo :: []) :: []
cedille-start _decls = (just "DeclsNil" , nothing , just _decls , inj₁ _posinfo :: []) :: (just "DeclsCons" , nothing , just _decls , inj₁ _ows :: inj₁ _decl :: inj₁ _decls :: []) :: []
cedille-start _decl = (just "Decl" , nothing , just _decl , inj₁ _posinfo :: inj₂ '(' :: inj₁ _ows :: inj₁ _var :: inj₁ _ows :: inj₂ ':' :: inj₁ _ows :: inj₁ _tk :: inj₁ _ows :: inj₂ ')' :: inj₁ _posinfo :: []) :: []
cedille-start _ctordeclsne = (just "CtordeclsneStart" , nothing , just _ctordeclsne , inj₁ _ows :: inj₁ _ctordecl :: []) :: (just "CtordeclsneNext" , nothing , just _ctordeclsne , inj₁ _ows :: inj₁ _ctordecl :: inj₁ _ows :: inj₂ ',' :: inj₁ _ctordeclsne :: []) :: []
cedille-start _ctordecls = (just "Ctordeclsne" , nothing , just _ctordecls , inj₁ _ctordeclsne :: []) :: (just "Ctordeclse" , nothing , just _ctordecls , inj₁ _posinfo :: []) :: []
cedille-start _ctordecl = (just "Ctordecl" , nothing , just _ctordecl , inj₁ _posinfo :: inj₁ _var :: inj₁ _ows :: inj₂ ':' :: inj₁ _ows :: inj₁ _type :: inj₁ _posinfo :: []) :: []
cedille-start _comment-star-41 = (just "P142" , nothing , just _comment-star-41 , inj₁ _anychar :: inj₁ _comment-star-41 :: []) :: (just "P141" , nothing , just _comment-star-41 , []) :: []
cedille-start _comment = (just "P143" , nothing , just _comment , inj₂ '%' :: inj₁ _comment-star-41 :: inj₂ '\n' :: []) :: []
cedille-start _cmds = (just "CmdsStart" , nothing , just _cmds , inj₁ _cmd :: []) :: (just "CmdsNext" , nothing , just _cmds , inj₁ _cmd :: inj₁ _ws :: inj₁ _cmds :: []) :: []
cedille-start _cmd = (just "TypeCmd" , nothing , just _cmd , inj₁ _maybeVarEq :: inj₁ _type :: inj₁ _ows :: inj₂ '⇐' :: inj₁ _ows :: inj₁ _kind :: inj₁ _ows :: inj₂ '.' :: []) :: (just "TermCmd" , nothing , just _cmd , inj₁ _maybeVarEq :: inj₁ _term :: inj₁ _ows :: inj₂ '⇐' :: inj₁ _ows :: inj₁ _type :: inj₁ _ows :: inj₂ '.' :: []) :: (just "Rec" , nothing , just _cmd , inj₁ _posinfo :: inj₂ 'r' :: inj₂ 'e' :: inj₂ 'c' :: inj₁ _ws :: inj₁ _var :: inj₁ _decls :: inj₁ _indices :: inj₁ _ows :: inj₂ '|' :: inj₁ _ctordecls :: inj₁ _ows :: inj₂ '=' :: inj₁ _ows :: inj₁ _type :: inj₁ _ws :: inj₂ 'w' :: inj₂ 'i' :: inj₂ 't' :: inj₂ 'h' :: inj₁ _udefs :: inj₁ _ows :: inj₂ '.' :: inj₁ _posinfo :: []) :: (just "Normalize" , nothing , just _cmd , inj₂ 'n' :: inj₂ 'o' :: inj₂ 'r' :: inj₂ 'm' :: inj₂ 'a' :: inj₂ 'l' :: inj₂ 'i' :: inj₂ 'z' :: inj₂ 'e' :: inj₁ _ws :: inj₁ _term :: inj₁ _ows :: inj₂ '.' :: []) :: (just "KindCmd" , nothing , just _cmd , inj₁ _maybeKvarEq :: inj₁ _kind :: inj₁ _ows :: inj₂ '⇐' :: inj₁ _ows :: inj₂ '□' :: inj₁ _ows :: inj₂ '.' :: []) :: (just "Import" , nothing , just _cmd , inj₂ 'i' :: inj₂ 'm' :: inj₂ 'p' :: inj₂ 'o' :: inj₂ 'r' :: inj₂ 't' :: inj₁ _ws :: inj₁ _var :: inj₁ _ows :: inj₂ '.' :: []) :: []
cedille-start _binder = (just "TpLambda" , nothing , just _binder , inj₂ 'λ' :: []) :: (just "Pi" , nothing , just _binder , inj₂ 'Π' :: []) :: (just "All" , nothing , just _binder , inj₂ '∀' :: []) :: []
cedille-start _aws-bar-44 = (just "P149" , nothing , just _aws-bar-44 , inj₁ _aws-bar-43 :: []) :: (just "P148" , nothing , just _aws-bar-44 , inj₂ '\n' :: []) :: []
cedille-start _aws-bar-43 = (just "P147" , nothing , just _aws-bar-43 , inj₁ _aws-bar-42 :: []) :: (just "P146" , nothing , just _aws-bar-43 , inj₂ '\t' :: []) :: []
cedille-start _aws-bar-42 = (just "P145" , nothing , just _aws-bar-42 , inj₁ _comment :: []) :: (just "P144" , nothing , just _aws-bar-42 , inj₂ ' ' :: []) :: []
cedille-start _aws = (just "P150" , nothing , just _aws , inj₁ _aws-bar-44 :: []) :: []
cedille-start _anychar-bar-40 = (just "P139" , nothing , just _anychar-bar-40 , inj₁ _anychar-bar-39 :: []) :: (just "P138" , nothing , just _anychar-bar-40 , inj₁ _alpha :: []) :: []
cedille-start _anychar-bar-39 = (just "P137" , nothing , just _anychar-bar-39 , inj₁ _anychar-bar-38 :: []) :: (just "P136" , nothing , just _anychar-bar-39 , inj₁ _numpunct :: []) :: []
cedille-start _anychar-bar-38 = (just "P135" , nothing , just _anychar-bar-38 , inj₁ _anychar-bar-37 :: []) :: (just "P134" , nothing , just _anychar-bar-38 , inj₂ '\t' :: []) :: []
cedille-start _anychar-bar-37 = (just "P133" , nothing , just _anychar-bar-37 , inj₁ _anychar-bar-36 :: []) :: (just "P132" , nothing , just _anychar-bar-37 , inj₂ ' ' :: []) :: []
cedille-start _anychar-bar-36 = (just "P131" , nothing , just _anychar-bar-36 , inj₁ _anychar-bar-35 :: []) :: (just "P130" , nothing , just _anychar-bar-36 , inj₂ '%' :: []) :: []
cedille-start _anychar-bar-35 = (just "P129" , nothing , just _anychar-bar-35 , inj₁ _anychar-bar-34 :: []) :: (just "P128" , nothing , just _anychar-bar-35 , inj₂ '□' :: []) :: []
cedille-start _anychar-bar-34 = (just "P127" , nothing , just _anychar-bar-34 , inj₁ _anychar-bar-33 :: []) :: (just "P126" , nothing , just _anychar-bar-34 , inj₂ 'Π' :: []) :: []
cedille-start _anychar-bar-33 = (just "P125" , nothing , just _anychar-bar-33 , inj₁ _anychar-bar-32 :: []) :: (just "P124" , nothing , just _anychar-bar-33 , inj₂ 'ι' :: []) :: []
cedille-start _anychar-bar-32 = (just "P123" , nothing , just _anychar-bar-32 , inj₁ _anychar-bar-31 :: []) :: (just "P122" , nothing , just _anychar-bar-32 , inj₂ 'λ' :: []) :: []
cedille-start _anychar-bar-31 = (just "P121" , nothing , just _anychar-bar-31 , inj₁ _anychar-bar-30 :: []) :: (just "P120" , nothing , just _anychar-bar-31 , inj₂ '∀' :: []) :: []
cedille-start _anychar-bar-30 = (just "P119" , nothing , just _anychar-bar-30 , inj₁ _anychar-bar-29 :: []) :: (just "P118" , nothing , just _anychar-bar-30 , inj₂ 'π' :: []) :: []
cedille-start _anychar-bar-29 = (just "P117" , nothing , just _anychar-bar-29 , inj₁ _anychar-bar-28 :: []) :: (just "P116" , nothing , just _anychar-bar-29 , inj₂ '★' :: []) :: []
cedille-start _anychar-bar-28 = (just "P115" , nothing , just _anychar-bar-28 , inj₁ _anychar-bar-27 :: []) :: (just "P114" , nothing , just _anychar-bar-28 , inj₂ '☆' :: []) :: []
cedille-start _anychar-bar-27 = (just "P113" , nothing , just _anychar-bar-27 , inj₁ _anychar-bar-26 :: []) :: (just "P112" , nothing , just _anychar-bar-27 , inj₂ '·' :: []) :: []
cedille-start _anychar-bar-26 = (just "P111" , nothing , just _anychar-bar-26 , inj₁ _anychar-bar-25 :: []) :: (just "P110" , nothing , just _anychar-bar-26 , inj₂ '⇐' :: []) :: []
cedille-start _anychar-bar-25 = (just "P109" , nothing , just _anychar-bar-25 , inj₁ _anychar-bar-24 :: []) :: (just "P108" , nothing , just _anychar-bar-25 , inj₂ '→' :: []) :: []
cedille-start _anychar-bar-24 = (just "P107" , nothing , just _anychar-bar-24 , inj₁ _anychar-bar-23 :: []) :: (just "P106" , nothing , just _anychar-bar-24 , inj₂ '↑' :: []) :: []
cedille-start _anychar-bar-23 = (just "P105" , nothing , just _anychar-bar-23 , inj₁ _anychar-bar-22 :: []) :: (just "P104" , nothing , just _anychar-bar-23 , inj₂ '𝓤' :: []) :: []
cedille-start _anychar-bar-22 = (just "P103" , nothing , just _anychar-bar-22 , inj₁ _anychar-bar-21 :: []) :: (just "P102" , nothing , just _anychar-bar-22 , inj₂ '●' :: []) :: []
cedille-start _anychar-bar-21 = (just "P101" , nothing , just _anychar-bar-21 , inj₁ _anychar-bar-20 :: []) :: (just "P100" , nothing , just _anychar-bar-21 , inj₂ '(' :: []) :: []
cedille-start _anychar-bar-20 = (just "P99" , nothing , just _anychar-bar-20 , inj₁ _anychar-bar-19 :: []) :: (just "P98" , nothing , just _anychar-bar-20 , inj₂ ')' :: []) :: []
cedille-start _anychar-bar-19 = (just "P97" , nothing , just _anychar-bar-19 , inj₁ _anychar-bar-18 :: []) :: (just "P96" , nothing , just _anychar-bar-19 , inj₂ ':' :: []) :: []
cedille-start _anychar-bar-18 = (just "P95" , nothing , just _anychar-bar-18 , inj₁ _anychar-bar-17 :: []) :: (just "P94" , nothing , just _anychar-bar-18 , inj₂ '.' :: []) :: []
cedille-start _anychar-bar-17 = (just "P93" , nothing , just _anychar-bar-17 , inj₁ _anychar-bar-16 :: []) :: (just "P92" , nothing , just _anychar-bar-17 , inj₂ '[' :: []) :: []
cedille-start _anychar-bar-16 = (just "P91" , nothing , just _anychar-bar-16 , inj₁ _anychar-bar-15 :: []) :: (just "P90" , nothing , just _anychar-bar-16 , inj₂ ']' :: []) :: []
cedille-start _anychar-bar-15 = (just "P89" , nothing , just _anychar-bar-15 , inj₁ _anychar-bar-14 :: []) :: (just "P88" , nothing , just _anychar-bar-15 , inj₂ ',' :: []) :: []
cedille-start _anychar-bar-14 = (just "P87" , nothing , just _anychar-bar-14 , inj₁ _anychar-bar-13 :: []) :: (just "P86" , nothing , just _anychar-bar-14 , inj₂ '!' :: []) :: []
cedille-start _anychar-bar-13 = (just "P85" , nothing , just _anychar-bar-13 , inj₁ _anychar-bar-12 :: []) :: (just "P84" , nothing , just _anychar-bar-13 , inj₂ '{' :: []) :: []
cedille-start _anychar-bar-12 = (just "P83" , nothing , just _anychar-bar-12 , inj₁ _anychar-bar-11 :: []) :: (just "P82" , nothing , just _anychar-bar-12 , inj₂ '}' :: []) :: []
cedille-start _anychar-bar-11 = (just "P81" , nothing , just _anychar-bar-11 , inj₂ '?' :: []) :: (just "P80" , nothing , just _anychar-bar-11 , inj₂ '⇒' :: []) :: []
cedille-start _anychar = (just "P140" , nothing , just _anychar , inj₁ _anychar-bar-40 :: []) :: []
cedille-start _alpha-range-2 = (just "P51" , nothing , just _alpha-range-2 , inj₂ 'Z' :: []) :: (just "P50" , nothing , just _alpha-range-2 , inj₂ 'Y' :: []) :: (just "P49" , nothing , just _alpha-range-2 , inj₂ 'X' :: []) :: (just "P48" , nothing , just _alpha-range-2 , inj₂ 'W' :: []) :: (just "P47" , nothing , just _alpha-range-2 , inj₂ 'V' :: []) :: (just "P46" , nothing , just _alpha-range-2 , inj₂ 'U' :: []) :: (just "P45" , nothing , just _alpha-range-2 , inj₂ 'T' :: []) :: (just "P44" , nothing , just _alpha-range-2 , inj₂ 'S' :: []) :: (just "P43" , nothing , just _alpha-range-2 , inj₂ 'R' :: []) :: (just "P42" , nothing , just _alpha-range-2 , inj₂ 'Q' :: []) :: (just "P41" , nothing , just _alpha-range-2 , inj₂ 'P' :: []) :: (just "P40" , nothing , just _alpha-range-2 , inj₂ 'O' :: []) :: (just "P39" , nothing , just _alpha-range-2 , inj₂ 'N' :: []) :: (just "P38" , nothing , just _alpha-range-2 , inj₂ 'M' :: []) :: (just "P37" , nothing , just _alpha-range-2 , inj₂ 'L' :: []) :: (just "P36" , nothing , just _alpha-range-2 , inj₂ 'K' :: []) :: (just "P35" , nothing , just _alpha-range-2 , inj₂ 'J' :: []) :: (just "P34" , nothing , just _alpha-range-2 , inj₂ 'I' :: []) :: (just "P33" , nothing , just _alpha-range-2 , inj₂ 'H' :: []) :: (just "P32" , nothing , just _alpha-range-2 , inj₂ 'G' :: []) :: (just "P31" , nothing , just _alpha-range-2 , inj₂ 'F' :: []) :: (just "P30" , nothing , just _alpha-range-2 , inj₂ 'E' :: []) :: (just "P29" , nothing , just _alpha-range-2 , inj₂ 'D' :: []) :: (just "P28" , nothing , just _alpha-range-2 , inj₂ 'C' :: []) :: (just "P27" , nothing , just _alpha-range-2 , inj₂ 'B' :: []) :: (just "P26" , nothing , just _alpha-range-2 , inj₂ 'A' :: []) :: []
cedille-start _alpha-range-1 = (just "P9" , nothing , just _alpha-range-1 , inj₂ 'j' :: []) :: (just "P8" , nothing , just _alpha-range-1 , inj₂ 'i' :: []) :: (just "P7" , nothing , just _alpha-range-1 , inj₂ 'h' :: []) :: (just "P6" , nothing , just _alpha-range-1 , inj₂ 'g' :: []) :: (just "P5" , nothing , just _alpha-range-1 , inj₂ 'f' :: []) :: (just "P4" , nothing , just _alpha-range-1 , inj₂ 'e' :: []) :: (just "P3" , nothing , just _alpha-range-1 , inj₂ 'd' :: []) :: (just "P25" , nothing , just _alpha-range-1 , inj₂ 'z' :: []) :: (just "P24" , nothing , just _alpha-range-1 , inj₂ 'y' :: []) :: (just "P23" , nothing , just _alpha-range-1 , inj₂ 'x' :: []) :: (just "P22" , nothing , just _alpha-range-1 , inj₂ 'w' :: []) :: (just "P21" , nothing , just _alpha-range-1 , inj₂ 'v' :: []) :: (just "P20" , nothing , just _alpha-range-1 , inj₂ 'u' :: []) :: (just "P2" , nothing , just _alpha-range-1 , inj₂ 'c' :: []) :: (just "P19" , nothing , just _alpha-range-1 , inj₂ 't' :: []) :: (just "P18" , nothing , just _alpha-range-1 , inj₂ 's' :: []) :: (just "P17" , nothing , just _alpha-range-1 , inj₂ 'r' :: []) :: (just "P16" , nothing , just _alpha-range-1 , inj₂ 'q' :: []) :: (just "P15" , nothing , just _alpha-range-1 , inj₂ 'p' :: []) :: (just "P14" , nothing , just _alpha-range-1 , inj₂ 'o' :: []) :: (just "P13" , nothing , just _alpha-range-1 , inj₂ 'n' :: []) :: (just "P12" , nothing , just _alpha-range-1 , inj₂ 'm' :: []) :: (just "P11" , nothing , just _alpha-range-1 , inj₂ 'l' :: []) :: (just "P10" , nothing , just _alpha-range-1 , inj₂ 'k' :: []) :: (just "P1" , nothing , just _alpha-range-1 , inj₂ 'b' :: []) :: (just "P0" , nothing , just _alpha-range-1 , inj₂ 'a' :: []) :: []
cedille-start _alpha-bar-3 = (just "P53" , nothing , just _alpha-bar-3 , inj₁ _alpha-range-2 :: []) :: (just "P52" , nothing , just _alpha-bar-3 , inj₁ _alpha-range-1 :: []) :: []
cedille-start _alpha = (just "P54" , nothing , just _alpha , inj₁ _alpha-bar-3 :: []) :: []


cedille-return : maybe gratr2-nt → 𝕃 gratr2-rule
cedille-return (just _term) = (nothing , nothing , just _term , inj₁ _ws :: inj₂ '·' :: inj₁ _ws :: inj₁ _type :: []) :: (nothing , nothing , just _term , inj₁ _ws :: inj₁ _maybeErased :: inj₁ _term :: []) :: []
cedille-return (just _ltype) = (nothing , nothing , just _ltype , inj₁ _ws :: inj₁ _lterm :: []) :: (nothing , nothing , just _ltype , inj₁ _ws :: inj₂ '·' :: inj₁ _ws :: inj₁ _ltype :: []) :: []
cedille-return (just _liftingType) = (nothing , nothing , just _liftingType , inj₁ _ows :: inj₂ '→' :: inj₁ _ows :: inj₁ _liftingType :: []) :: []
cedille-return (just _kind) = (nothing , nothing , just _kind , inj₁ _ows :: inj₂ '→' :: inj₁ _ows :: inj₁ _kind :: []) :: []
cedille-return _ = []

cedille-rtn : gratr2-rtn
cedille-rtn = record { start = _start ; _eq_ = gratr2-nt-eq ; gratr2-start = cedille-start ; gratr2-return = cedille-return }

open import run ptr
open noderiv

------------------------------------------
-- Length-decreasing rules
------------------------------------------

len-dec-rewrite : Run → maybe (Run × ℕ)
len-dec-rewrite {- Abs-} ((Id "Abs") :: (ParseTree (parsed-posinfo x0)) :: (ParseTree (parsed-binder x1)) :: (ParseTree parsed-ows) :: (ParseTree (parsed-var x2)) :: (ParseTree parsed-ows) :: (InputChar ':') :: (ParseTree parsed-ows) :: (ParseTree (parsed-tk x3)) :: (ParseTree parsed-ows) :: (InputChar '.') :: (ParseTree parsed-ows) :: _::_(ParseTree (parsed-type x4)) rest) = just (ParseTree (parsed-type (norm-type (Abs x0 x1 x2 x3 x4))) ::' rest , 13)
len-dec-rewrite {- All-} ((Id "All") :: _::_(InputChar '∀') rest) = just (ParseTree (parsed-binder (norm-binder All)) ::' rest , 2)
len-dec-rewrite {- App-} ((ParseTree (parsed-term x0)) :: (ParseTree parsed-ws) :: (ParseTree (parsed-maybeErased x1)) :: _::_(ParseTree (parsed-term x2)) rest) = just (ParseTree (parsed-term (norm-term (App x0 x1 x2))) ::' rest , 4)
len-dec-rewrite {- AppTp-} ((ParseTree (parsed-term x0)) :: (ParseTree parsed-ws) :: (InputChar '·') :: (ParseTree parsed-ws) :: _::_(ParseTree (parsed-type x1)) rest) = just (ParseTree (parsed-term (norm-term (AppTp x0 x1))) ::' rest , 5)
len-dec-rewrite {- Cmds-} ((Id "Cmds") :: (ParseTree parsed-ows) :: (ParseTree (parsed-cmds x0)) :: _::_(ParseTree parsed-ows) rest) = just (ParseTree (parsed-start (norm-start (Cmds x0))) ::' rest , 4)
len-dec-rewrite {- CmdsNext-} ((Id "CmdsNext") :: (ParseTree (parsed-cmd x0)) :: (ParseTree parsed-ws) :: _::_(ParseTree (parsed-cmds x1)) rest) = just (ParseTree (parsed-cmds (norm-cmds (CmdsNext x0 x1))) ::' rest , 4)
len-dec-rewrite {- CmdsStart-} ((Id "CmdsStart") :: _::_(ParseTree (parsed-cmd x0)) rest) = just (ParseTree (parsed-cmds (norm-cmds (CmdsStart x0))) ::' rest , 2)
len-dec-rewrite {- Ctordecl-} ((Id "Ctordecl") :: (ParseTree (parsed-posinfo x0)) :: (ParseTree (parsed-var x1)) :: (ParseTree parsed-ows) :: (InputChar ':') :: (ParseTree parsed-ows) :: (ParseTree (parsed-type x2)) :: _::_(ParseTree (parsed-posinfo x3)) rest) = just (ParseTree (parsed-ctordecl (norm-ctordecl (Ctordecl x0 x1 x2 x3))) ::' rest , 8)
len-dec-rewrite {- Ctordeclse-} ((Id "Ctordeclse") :: _::_(ParseTree (parsed-posinfo x0)) rest) = just (ParseTree (parsed-ctordecls (norm-ctordecls (Ctordeclse x0))) ::' rest , 2)
len-dec-rewrite {- Ctordeclsne-} ((Id "Ctordeclsne") :: _::_(ParseTree (parsed-ctordeclsne x0)) rest) = just (ParseTree (parsed-ctordecls (norm-ctordecls (Ctordeclsne x0))) ::' rest , 2)
len-dec-rewrite {- CtordeclsneNext-} ((Id "CtordeclsneNext") :: (ParseTree parsed-ows) :: (ParseTree (parsed-ctordecl x0)) :: (ParseTree parsed-ows) :: (InputChar ',') :: _::_(ParseTree (parsed-ctordeclsne x1)) rest) = just (ParseTree (parsed-ctordeclsne (norm-ctordeclsne (CtordeclsneNext x0 x1))) ::' rest , 6)
len-dec-rewrite {- CtordeclsneStart-} ((Id "CtordeclsneStart") :: (ParseTree parsed-ows) :: _::_(ParseTree (parsed-ctordecl x0)) rest) = just (ParseTree (parsed-ctordeclsne (norm-ctordeclsne (CtordeclsneStart x0))) ::' rest , 3)
len-dec-rewrite {- Decl-} ((Id "Decl") :: (ParseTree (parsed-posinfo x0)) :: (InputChar '(') :: (ParseTree parsed-ows) :: (ParseTree (parsed-var x1)) :: (ParseTree parsed-ows) :: (InputChar ':') :: (ParseTree parsed-ows) :: (ParseTree (parsed-tk x2)) :: (ParseTree parsed-ows) :: (InputChar ')') :: _::_(ParseTree (parsed-posinfo x3)) rest) = just (ParseTree (parsed-decl (norm-decl (Decl x0 x1 x2 x3))) ::' rest , 12)
len-dec-rewrite {- DeclsCons-} ((Id "DeclsCons") :: (ParseTree parsed-ows) :: (ParseTree (parsed-decl x0)) :: _::_(ParseTree (parsed-decls x1)) rest) = just (ParseTree (parsed-decls (norm-decls (DeclsCons x0 x1))) ::' rest , 4)
len-dec-rewrite {- DeclsNil-} ((Id "DeclsNil") :: _::_(ParseTree (parsed-posinfo x0)) rest) = just (ParseTree (parsed-decls (norm-decls (DeclsNil x0))) ::' rest , 2)
len-dec-rewrite {- Erased-} ((Id "Erased") :: (InputChar '-') :: _::_(ParseTree parsed-ows) rest) = just (ParseTree (parsed-maybeErased (norm-maybeErased Erased)) ::' rest , 3)
len-dec-rewrite {- ErasedLambda-} ((Id "ErasedLambda") :: _::_(InputChar 'Λ') rest) = just (ParseTree (parsed-lam (norm-lam ErasedLambda)) ::' rest , 2)
len-dec-rewrite {- Hole-} ((Id "Hole") :: (ParseTree (parsed-posinfo x0)) :: _::_(InputChar '●') rest) = just (ParseTree (parsed-lterm (norm-term (Hole x0))) ::' rest , 3)
len-dec-rewrite {- Import-} ((Id "Import") :: (InputChar 'i') :: (InputChar 'm') :: (InputChar 'p') :: (InputChar 'o') :: (InputChar 'r') :: (InputChar 't') :: (ParseTree parsed-ws) :: (ParseTree (parsed-var x0)) :: (ParseTree parsed-ows) :: _::_(InputChar '.') rest) = just (ParseTree (parsed-cmd (norm-cmd (Import x0))) ::' rest , 11)
len-dec-rewrite {- Indicese-} ((Id "Indicese") :: _::_(ParseTree (parsed-posinfo x0)) rest) = just (ParseTree (parsed-indices (norm-indices (Indicese x0))) ::' rest , 2)
len-dec-rewrite {- Indicesne-} ((Id "Indicesne") :: (ParseTree parsed-ows) :: (InputChar ':') :: _::_(ParseTree (parsed-decls x0)) rest) = just (ParseTree (parsed-indices (norm-indices (Indicesne x0))) ::' rest , 4)
len-dec-rewrite {- KeptLambda-} ((Id "KeptLambda") :: _::_(InputChar 'λ') rest) = just (ParseTree (parsed-lam (norm-lam KeptLambda)) ::' rest , 2)
len-dec-rewrite {- KindCmd-} ((Id "KindCmd") :: (ParseTree (parsed-maybeKvarEq x0)) :: (ParseTree (parsed-kind x1)) :: (ParseTree parsed-ows) :: (InputChar '⇐') :: (ParseTree parsed-ows) :: (InputChar '□') :: (ParseTree parsed-ows) :: _::_(InputChar '.') rest) = just (ParseTree (parsed-cmd (norm-cmd (KindCmd x0 x1))) ::' rest , 9)
len-dec-rewrite {- KndArrow-} ((ParseTree (parsed-kind x0)) :: (ParseTree parsed-ows) :: (InputChar '→') :: (ParseTree parsed-ows) :: _::_(ParseTree (parsed-kind x1)) rest) = just (ParseTree (parsed-kind (norm-kind (KndArrow x0 x1))) ::' rest , 5)
len-dec-rewrite {- KndParens-} ((Id "KndParens") :: (ParseTree (parsed-posinfo x0)) :: (InputChar '(') :: (ParseTree parsed-ows) :: (ParseTree (parsed-kind x1)) :: (ParseTree parsed-ows) :: (InputChar ')') :: _::_(ParseTree (parsed-posinfo x2)) rest) = just (ParseTree (parsed-kind (norm-kind (KndParens x0 x1 x2))) ::' rest , 8)
len-dec-rewrite {- KndPi-} ((Id "KndPi") :: (ParseTree (parsed-posinfo x0)) :: (InputChar 'Π') :: (ParseTree parsed-ows) :: (ParseTree (parsed-var x1)) :: (ParseTree parsed-ows) :: (InputChar ':') :: (ParseTree parsed-ows) :: (ParseTree (parsed-tk x2)) :: (ParseTree parsed-ows) :: (InputChar '.') :: (ParseTree parsed-ows) :: _::_(ParseTree (parsed-kind x3)) rest) = just (ParseTree (parsed-kind (norm-kind (KndPi x0 x1 x2 x3))) ::' rest , 13)
len-dec-rewrite {- KndTpArrow-} ((Id "KndTpArrow") :: (ParseTree (parsed-ltype x0)) :: (ParseTree parsed-ows) :: (InputChar '→') :: (ParseTree parsed-ows) :: _::_(ParseTree (parsed-kind x1)) rest) = just (ParseTree (parsed-kind (norm-kind (KndTpArrow x0 x1))) ::' rest , 6)
len-dec-rewrite {- KndVar-} ((Id "KndVar") :: (ParseTree (parsed-posinfo x0)) :: _::_(ParseTree (parsed-kvar x1)) rest) = just (ParseTree (parsed-kind (norm-kind (KndVar x0 x1))) ::' rest , 3)
len-dec-rewrite {- KvarEq-} ((Id "KvarEq") :: (ParseTree (parsed-kvar x0)) :: (ParseTree parsed-ows) :: (InputChar '=') :: _::_(ParseTree parsed-ows) rest) = just (ParseTree (parsed-maybeKvarEq (norm-maybeKvarEq (KvarEq x0))) ::' rest , 5)
len-dec-rewrite {- Lam-} ((Id "Lam") :: (ParseTree (parsed-posinfo x0)) :: (ParseTree (parsed-lam x1)) :: (ParseTree parsed-ows) :: (ParseTree (parsed-var x2)) :: (ParseTree (parsed-optClass x3)) :: (ParseTree parsed-ows) :: (InputChar '.') :: (ParseTree parsed-ows) :: _::_(ParseTree (parsed-term x4)) rest) = just (ParseTree (parsed-term (norm-term (Lam x0 x1 x2 x3 x4))) ::' rest , 10)
len-dec-rewrite {- Lft-} ((Id "Lft") :: (ParseTree (parsed-posinfo x0)) :: (InputChar '↑') :: (ParseTree parsed-ows) :: (ParseTree (parsed-term x1)) :: (ParseTree parsed-ows) :: (InputChar ':') :: (ParseTree parsed-ows) :: _::_(ParseTree (parsed-lliftingType x2)) rest) = just (ParseTree (parsed-ltype (norm-type (Lft x0 x1 x2))) ::' rest , 9)
len-dec-rewrite {- LiftArrow-} ((ParseTree (parsed-liftingType x0)) :: (ParseTree parsed-ows) :: (InputChar '→') :: (ParseTree parsed-ows) :: _::_(ParseTree (parsed-liftingType x1)) rest) = just (ParseTree (parsed-liftingType (norm-liftingType (LiftArrow x0 x1))) ::' rest , 5)
len-dec-rewrite {- LiftParens-} ((Id "LiftParens") :: (ParseTree (parsed-posinfo x0)) :: (InputChar '(') :: (ParseTree parsed-ows) :: (ParseTree (parsed-liftingType x1)) :: (ParseTree parsed-ows) :: (InputChar ')') :: _::_(ParseTree (parsed-posinfo x2)) rest) = just (ParseTree (parsed-lliftingType (norm-liftingType (LiftParens x0 x1 x2))) ::' rest , 8)
len-dec-rewrite {- LiftPi-} ((Id "LiftPi") :: (ParseTree (parsed-posinfo x0)) :: (InputChar 'Π') :: (ParseTree parsed-ows) :: (ParseTree (parsed-var x1)) :: (ParseTree parsed-ows) :: (InputChar ':') :: (ParseTree parsed-ows) :: (ParseTree (parsed-type x2)) :: (ParseTree parsed-ows) :: (InputChar '.') :: (ParseTree parsed-ows) :: _::_(ParseTree (parsed-liftingType x3)) rest) = just (ParseTree (parsed-liftingType (norm-liftingType (LiftPi x0 x1 x2 x3))) ::' rest , 13)
len-dec-rewrite {- LiftStar-} ((Id "LiftStar") :: (ParseTree (parsed-posinfo x0)) :: _::_(InputChar '☆') rest) = just (ParseTree (parsed-liftingType (norm-liftingType (LiftStar x0))) ::' rest , 3)
len-dec-rewrite {- LiftTpArrow-} ((Id "LiftTpArrow") :: (ParseTree (parsed-type x0)) :: (ParseTree parsed-ows) :: (InputChar '→') :: (ParseTree parsed-ows) :: _::_(ParseTree (parsed-liftingType x1)) rest) = just (ParseTree (parsed-liftingType (norm-liftingType (LiftTpArrow x0 x1))) ::' rest , 6)
len-dec-rewrite {- Normalize-} ((Id "Normalize") :: (InputChar 'n') :: (InputChar 'o') :: (InputChar 'r') :: (InputChar 'm') :: (InputChar 'a') :: (InputChar 'l') :: (InputChar 'i') :: (InputChar 'z') :: (InputChar 'e') :: (ParseTree parsed-ws) :: (ParseTree (parsed-term x0)) :: (ParseTree parsed-ows) :: _::_(InputChar '.') rest) = just (ParseTree (parsed-cmd (norm-cmd (Normalize x0))) ::' rest , 14)
len-dec-rewrite {- P0-} ((Id "P0") :: _::_(InputChar 'a') rest) = just (ParseTree (parsed-alpha-range-1 (string-append 0 (char-to-string 'a'))) ::' rest , 2)
len-dec-rewrite {- P1-} ((Id "P1") :: _::_(InputChar 'b') rest) = just (ParseTree (parsed-alpha-range-1 (string-append 0 (char-to-string 'b'))) ::' rest , 2)
len-dec-rewrite {- P10-} ((Id "P10") :: _::_(InputChar 'k') rest) = just (ParseTree (parsed-alpha-range-1 (string-append 0 (char-to-string 'k'))) ::' rest , 2)
len-dec-rewrite {- P100-} ((Id "P100") :: _::_(InputChar '(') rest) = just (ParseTree parsed-anychar-bar-21 ::' rest , 2)
len-dec-rewrite {- P101-} ((Id "P101") :: _::_(ParseTree parsed-anychar-bar-20) rest) = just (ParseTree parsed-anychar-bar-21 ::' rest , 2)
len-dec-rewrite {- P102-} ((Id "P102") :: _::_(InputChar '●') rest) = just (ParseTree parsed-anychar-bar-22 ::' rest , 2)
len-dec-rewrite {- P103-} ((Id "P103") :: _::_(ParseTree parsed-anychar-bar-21) rest) = just (ParseTree parsed-anychar-bar-22 ::' rest , 2)
len-dec-rewrite {- P104-} ((Id "P104") :: _::_(InputChar '𝓤') rest) = just (ParseTree parsed-anychar-bar-23 ::' rest , 2)
len-dec-rewrite {- P105-} ((Id "P105") :: _::_(ParseTree parsed-anychar-bar-22) rest) = just (ParseTree parsed-anychar-bar-23 ::' rest , 2)
len-dec-rewrite {- P106-} ((Id "P106") :: _::_(InputChar '↑') rest) = just (ParseTree parsed-anychar-bar-24 ::' rest , 2)
len-dec-rewrite {- P107-} ((Id "P107") :: _::_(ParseTree parsed-anychar-bar-23) rest) = just (ParseTree parsed-anychar-bar-24 ::' rest , 2)
len-dec-rewrite {- P108-} ((Id "P108") :: _::_(InputChar '→') rest) = just (ParseTree parsed-anychar-bar-25 ::' rest , 2)
len-dec-rewrite {- P109-} ((Id "P109") :: _::_(ParseTree parsed-anychar-bar-24) rest) = just (ParseTree parsed-anychar-bar-25 ::' rest , 2)
len-dec-rewrite {- P11-} ((Id "P11") :: _::_(InputChar 'l') rest) = just (ParseTree (parsed-alpha-range-1 (string-append 0 (char-to-string 'l'))) ::' rest , 2)
len-dec-rewrite {- P110-} ((Id "P110") :: _::_(InputChar '⇐') rest) = just (ParseTree parsed-anychar-bar-26 ::' rest , 2)
len-dec-rewrite {- P111-} ((Id "P111") :: _::_(ParseTree parsed-anychar-bar-25) rest) = just (ParseTree parsed-anychar-bar-26 ::' rest , 2)
len-dec-rewrite {- P112-} ((Id "P112") :: _::_(InputChar '·') rest) = just (ParseTree parsed-anychar-bar-27 ::' rest , 2)
len-dec-rewrite {- P113-} ((Id "P113") :: _::_(ParseTree parsed-anychar-bar-26) rest) = just (ParseTree parsed-anychar-bar-27 ::' rest , 2)
len-dec-rewrite {- P114-} ((Id "P114") :: _::_(InputChar '☆') rest) = just (ParseTree parsed-anychar-bar-28 ::' rest , 2)
len-dec-rewrite {- P115-} ((Id "P115") :: _::_(ParseTree parsed-anychar-bar-27) rest) = just (ParseTree parsed-anychar-bar-28 ::' rest , 2)
len-dec-rewrite {- P116-} ((Id "P116") :: _::_(InputChar '★') rest) = just (ParseTree parsed-anychar-bar-29 ::' rest , 2)
len-dec-rewrite {- P117-} ((Id "P117") :: _::_(ParseTree parsed-anychar-bar-28) rest) = just (ParseTree parsed-anychar-bar-29 ::' rest , 2)
len-dec-rewrite {- P118-} ((Id "P118") :: _::_(InputChar 'π') rest) = just (ParseTree parsed-anychar-bar-30 ::' rest , 2)
len-dec-rewrite {- P119-} ((Id "P119") :: _::_(ParseTree parsed-anychar-bar-29) rest) = just (ParseTree parsed-anychar-bar-30 ::' rest , 2)
len-dec-rewrite {- P12-} ((Id "P12") :: _::_(InputChar 'm') rest) = just (ParseTree (parsed-alpha-range-1 (string-append 0 (char-to-string 'm'))) ::' rest , 2)
len-dec-rewrite {- P120-} ((Id "P120") :: _::_(InputChar '∀') rest) = just (ParseTree parsed-anychar-bar-31 ::' rest , 2)
len-dec-rewrite {- P121-} ((Id "P121") :: _::_(ParseTree parsed-anychar-bar-30) rest) = just (ParseTree parsed-anychar-bar-31 ::' rest , 2)
len-dec-rewrite {- P122-} ((Id "P122") :: _::_(InputChar 'λ') rest) = just (ParseTree parsed-anychar-bar-32 ::' rest , 2)
len-dec-rewrite {- P123-} ((Id "P123") :: _::_(ParseTree parsed-anychar-bar-31) rest) = just (ParseTree parsed-anychar-bar-32 ::' rest , 2)
len-dec-rewrite {- P124-} ((Id "P124") :: _::_(InputChar 'ι') rest) = just (ParseTree parsed-anychar-bar-33 ::' rest , 2)
len-dec-rewrite {- P125-} ((Id "P125") :: _::_(ParseTree parsed-anychar-bar-32) rest) = just (ParseTree parsed-anychar-bar-33 ::' rest , 2)
len-dec-rewrite {- P126-} ((Id "P126") :: _::_(InputChar 'Π') rest) = just (ParseTree parsed-anychar-bar-34 ::' rest , 2)
len-dec-rewrite {- P127-} ((Id "P127") :: _::_(ParseTree parsed-anychar-bar-33) rest) = just (ParseTree parsed-anychar-bar-34 ::' rest , 2)
len-dec-rewrite {- P128-} ((Id "P128") :: _::_(InputChar '□') rest) = just (ParseTree parsed-anychar-bar-35 ::' rest , 2)
len-dec-rewrite {- P129-} ((Id "P129") :: _::_(ParseTree parsed-anychar-bar-34) rest) = just (ParseTree parsed-anychar-bar-35 ::' rest , 2)
len-dec-rewrite {- P13-} ((Id "P13") :: _::_(InputChar 'n') rest) = just (ParseTree (parsed-alpha-range-1 (string-append 0 (char-to-string 'n'))) ::' rest , 2)
len-dec-rewrite {- P130-} ((Id "P130") :: _::_(InputChar '%') rest) = just (ParseTree parsed-anychar-bar-36 ::' rest , 2)
len-dec-rewrite {- P131-} ((Id "P131") :: _::_(ParseTree parsed-anychar-bar-35) rest) = just (ParseTree parsed-anychar-bar-36 ::' rest , 2)
len-dec-rewrite {- P132-} ((Id "P132") :: _::_(InputChar ' ') rest) = just (ParseTree parsed-anychar-bar-37 ::' rest , 2)
len-dec-rewrite {- P133-} ((Id "P133") :: _::_(ParseTree parsed-anychar-bar-36) rest) = just (ParseTree parsed-anychar-bar-37 ::' rest , 2)
len-dec-rewrite {- P134-} ((Id "P134") :: _::_(InputChar '\t') rest) = just (ParseTree parsed-anychar-bar-38 ::' rest , 2)
len-dec-rewrite {- P135-} ((Id "P135") :: _::_(ParseTree parsed-anychar-bar-37) rest) = just (ParseTree parsed-anychar-bar-38 ::' rest , 2)
len-dec-rewrite {- P136-} ((Id "P136") :: _::_(ParseTree (parsed-numpunct x0)) rest) = just (ParseTree parsed-anychar-bar-39 ::' rest , 2)
len-dec-rewrite {- P137-} ((Id "P137") :: _::_(ParseTree parsed-anychar-bar-38) rest) = just (ParseTree parsed-anychar-bar-39 ::' rest , 2)
len-dec-rewrite {- P138-} ((Id "P138") :: _::_(ParseTree (parsed-alpha x0)) rest) = just (ParseTree parsed-anychar-bar-40 ::' rest , 2)
len-dec-rewrite {- P139-} ((Id "P139") :: _::_(ParseTree parsed-anychar-bar-39) rest) = just (ParseTree parsed-anychar-bar-40 ::' rest , 2)
len-dec-rewrite {- P14-} ((Id "P14") :: _::_(InputChar 'o') rest) = just (ParseTree (parsed-alpha-range-1 (string-append 0 (char-to-string 'o'))) ::' rest , 2)
len-dec-rewrite {- P140-} ((Id "P140") :: _::_(ParseTree parsed-anychar-bar-40) rest) = just (ParseTree parsed-anychar ::' rest , 2)
len-dec-rewrite {- P142-} ((Id "P142") :: (ParseTree parsed-anychar) :: _::_(ParseTree parsed-comment-star-41) rest) = just (ParseTree parsed-comment-star-41 ::' rest , 3)
len-dec-rewrite {- P143-} ((Id "P143") :: (InputChar '%') :: (ParseTree parsed-comment-star-41) :: _::_(InputChar '\n') rest) = just (ParseTree parsed-comment ::' rest , 4)
len-dec-rewrite {- P144-} ((Id "P144") :: _::_(InputChar ' ') rest) = just (ParseTree parsed-aws-bar-42 ::' rest , 2)
len-dec-rewrite {- P145-} ((Id "P145") :: _::_(ParseTree parsed-comment) rest) = just (ParseTree parsed-aws-bar-42 ::' rest , 2)
len-dec-rewrite {- P146-} ((Id "P146") :: _::_(InputChar '\t') rest) = just (ParseTree parsed-aws-bar-43 ::' rest , 2)
len-dec-rewrite {- P147-} ((Id "P147") :: _::_(ParseTree parsed-aws-bar-42) rest) = just (ParseTree parsed-aws-bar-43 ::' rest , 2)
len-dec-rewrite {- P148-} ((Id "P148") :: _::_(InputChar '\n') rest) = just (ParseTree parsed-aws-bar-44 ::' rest , 2)
len-dec-rewrite {- P149-} ((Id "P149") :: _::_(ParseTree parsed-aws-bar-43) rest) = just (ParseTree parsed-aws-bar-44 ::' rest , 2)
len-dec-rewrite {- P15-} ((Id "P15") :: _::_(InputChar 'p') rest) = just (ParseTree (parsed-alpha-range-1 (string-append 0 (char-to-string 'p'))) ::' rest , 2)
len-dec-rewrite {- P150-} ((Id "P150") :: _::_(ParseTree parsed-aws-bar-44) rest) = just (ParseTree parsed-aws ::' rest , 2)
len-dec-rewrite {- P151-} ((Id "P151") :: _::_(ParseTree parsed-aws) rest) = just (ParseTree parsed-ws-plus-45 ::' rest , 2)
len-dec-rewrite {- P152-} ((Id "P152") :: (ParseTree parsed-aws) :: _::_(ParseTree parsed-ws-plus-45) rest) = just (ParseTree parsed-ws-plus-45 ::' rest , 3)
len-dec-rewrite {- P153-} ((Id "P153") :: _::_(ParseTree parsed-ws-plus-45) rest) = just (ParseTree parsed-ws ::' rest , 2)
len-dec-rewrite {- P155-} ((Id "P155") :: (ParseTree parsed-aws) :: _::_(ParseTree parsed-ows-star-46) rest) = just (ParseTree parsed-ows-star-46 ::' rest , 3)
len-dec-rewrite {- P156-} ((Id "P156") :: _::_(ParseTree parsed-ows-star-46) rest) = just (ParseTree parsed-ows ::' rest , 2)
len-dec-rewrite {- P16-} ((Id "P16") :: _::_(InputChar 'q') rest) = just (ParseTree (parsed-alpha-range-1 (string-append 0 (char-to-string 'q'))) ::' rest , 2)
len-dec-rewrite {- P17-} ((Id "P17") :: _::_(InputChar 'r') rest) = just (ParseTree (parsed-alpha-range-1 (string-append 0 (char-to-string 'r'))) ::' rest , 2)
len-dec-rewrite {- P18-} ((Id "P18") :: _::_(InputChar 's') rest) = just (ParseTree (parsed-alpha-range-1 (string-append 0 (char-to-string 's'))) ::' rest , 2)
len-dec-rewrite {- P19-} ((Id "P19") :: _::_(InputChar 't') rest) = just (ParseTree (parsed-alpha-range-1 (string-append 0 (char-to-string 't'))) ::' rest , 2)
len-dec-rewrite {- P2-} ((Id "P2") :: _::_(InputChar 'c') rest) = just (ParseTree (parsed-alpha-range-1 (string-append 0 (char-to-string 'c'))) ::' rest , 2)
len-dec-rewrite {- P20-} ((Id "P20") :: _::_(InputChar 'u') rest) = just (ParseTree (parsed-alpha-range-1 (string-append 0 (char-to-string 'u'))) ::' rest , 2)
len-dec-rewrite {- P21-} ((Id "P21") :: _::_(InputChar 'v') rest) = just (ParseTree (parsed-alpha-range-1 (string-append 0 (char-to-string 'v'))) ::' rest , 2)
len-dec-rewrite {- P22-} ((Id "P22") :: _::_(InputChar 'w') rest) = just (ParseTree (parsed-alpha-range-1 (string-append 0 (char-to-string 'w'))) ::' rest , 2)
len-dec-rewrite {- P23-} ((Id "P23") :: _::_(InputChar 'x') rest) = just (ParseTree (parsed-alpha-range-1 (string-append 0 (char-to-string 'x'))) ::' rest , 2)
len-dec-rewrite {- P24-} ((Id "P24") :: _::_(InputChar 'y') rest) = just (ParseTree (parsed-alpha-range-1 (string-append 0 (char-to-string 'y'))) ::' rest , 2)
len-dec-rewrite {- P25-} ((Id "P25") :: _::_(InputChar 'z') rest) = just (ParseTree (parsed-alpha-range-1 (string-append 0 (char-to-string 'z'))) ::' rest , 2)
len-dec-rewrite {- P26-} ((Id "P26") :: _::_(InputChar 'A') rest) = just (ParseTree (parsed-alpha-range-2 (string-append 0 (char-to-string 'A'))) ::' rest , 2)
len-dec-rewrite {- P27-} ((Id "P27") :: _::_(InputChar 'B') rest) = just (ParseTree (parsed-alpha-range-2 (string-append 0 (char-to-string 'B'))) ::' rest , 2)
len-dec-rewrite {- P28-} ((Id "P28") :: _::_(InputChar 'C') rest) = just (ParseTree (parsed-alpha-range-2 (string-append 0 (char-to-string 'C'))) ::' rest , 2)
len-dec-rewrite {- P29-} ((Id "P29") :: _::_(InputChar 'D') rest) = just (ParseTree (parsed-alpha-range-2 (string-append 0 (char-to-string 'D'))) ::' rest , 2)
len-dec-rewrite {- P3-} ((Id "P3") :: _::_(InputChar 'd') rest) = just (ParseTree (parsed-alpha-range-1 (string-append 0 (char-to-string 'd'))) ::' rest , 2)
len-dec-rewrite {- P30-} ((Id "P30") :: _::_(InputChar 'E') rest) = just (ParseTree (parsed-alpha-range-2 (string-append 0 (char-to-string 'E'))) ::' rest , 2)
len-dec-rewrite {- P31-} ((Id "P31") :: _::_(InputChar 'F') rest) = just (ParseTree (parsed-alpha-range-2 (string-append 0 (char-to-string 'F'))) ::' rest , 2)
len-dec-rewrite {- P32-} ((Id "P32") :: _::_(InputChar 'G') rest) = just (ParseTree (parsed-alpha-range-2 (string-append 0 (char-to-string 'G'))) ::' rest , 2)
len-dec-rewrite {- P33-} ((Id "P33") :: _::_(InputChar 'H') rest) = just (ParseTree (parsed-alpha-range-2 (string-append 0 (char-to-string 'H'))) ::' rest , 2)
len-dec-rewrite {- P34-} ((Id "P34") :: _::_(InputChar 'I') rest) = just (ParseTree (parsed-alpha-range-2 (string-append 0 (char-to-string 'I'))) ::' rest , 2)
len-dec-rewrite {- P35-} ((Id "P35") :: _::_(InputChar 'J') rest) = just (ParseTree (parsed-alpha-range-2 (string-append 0 (char-to-string 'J'))) ::' rest , 2)
len-dec-rewrite {- P36-} ((Id "P36") :: _::_(InputChar 'K') rest) = just (ParseTree (parsed-alpha-range-2 (string-append 0 (char-to-string 'K'))) ::' rest , 2)
len-dec-rewrite {- P37-} ((Id "P37") :: _::_(InputChar 'L') rest) = just (ParseTree (parsed-alpha-range-2 (string-append 0 (char-to-string 'L'))) ::' rest , 2)
len-dec-rewrite {- P38-} ((Id "P38") :: _::_(InputChar 'M') rest) = just (ParseTree (parsed-alpha-range-2 (string-append 0 (char-to-string 'M'))) ::' rest , 2)
len-dec-rewrite {- P39-} ((Id "P39") :: _::_(InputChar 'N') rest) = just (ParseTree (parsed-alpha-range-2 (string-append 0 (char-to-string 'N'))) ::' rest , 2)
len-dec-rewrite {- P4-} ((Id "P4") :: _::_(InputChar 'e') rest) = just (ParseTree (parsed-alpha-range-1 (string-append 0 (char-to-string 'e'))) ::' rest , 2)
len-dec-rewrite {- P40-} ((Id "P40") :: _::_(InputChar 'O') rest) = just (ParseTree (parsed-alpha-range-2 (string-append 0 (char-to-string 'O'))) ::' rest , 2)
len-dec-rewrite {- P41-} ((Id "P41") :: _::_(InputChar 'P') rest) = just (ParseTree (parsed-alpha-range-2 (string-append 0 (char-to-string 'P'))) ::' rest , 2)
len-dec-rewrite {- P42-} ((Id "P42") :: _::_(InputChar 'Q') rest) = just (ParseTree (parsed-alpha-range-2 (string-append 0 (char-to-string 'Q'))) ::' rest , 2)
len-dec-rewrite {- P43-} ((Id "P43") :: _::_(InputChar 'R') rest) = just (ParseTree (parsed-alpha-range-2 (string-append 0 (char-to-string 'R'))) ::' rest , 2)
len-dec-rewrite {- P44-} ((Id "P44") :: _::_(InputChar 'S') rest) = just (ParseTree (parsed-alpha-range-2 (string-append 0 (char-to-string 'S'))) ::' rest , 2)
len-dec-rewrite {- P45-} ((Id "P45") :: _::_(InputChar 'T') rest) = just (ParseTree (parsed-alpha-range-2 (string-append 0 (char-to-string 'T'))) ::' rest , 2)
len-dec-rewrite {- P46-} ((Id "P46") :: _::_(InputChar 'U') rest) = just (ParseTree (parsed-alpha-range-2 (string-append 0 (char-to-string 'U'))) ::' rest , 2)
len-dec-rewrite {- P47-} ((Id "P47") :: _::_(InputChar 'V') rest) = just (ParseTree (parsed-alpha-range-2 (string-append 0 (char-to-string 'V'))) ::' rest , 2)
len-dec-rewrite {- P48-} ((Id "P48") :: _::_(InputChar 'W') rest) = just (ParseTree (parsed-alpha-range-2 (string-append 0 (char-to-string 'W'))) ::' rest , 2)
len-dec-rewrite {- P49-} ((Id "P49") :: _::_(InputChar 'X') rest) = just (ParseTree (parsed-alpha-range-2 (string-append 0 (char-to-string 'X'))) ::' rest , 2)
len-dec-rewrite {- P5-} ((Id "P5") :: _::_(InputChar 'f') rest) = just (ParseTree (parsed-alpha-range-1 (string-append 0 (char-to-string 'f'))) ::' rest , 2)
len-dec-rewrite {- P50-} ((Id "P50") :: _::_(InputChar 'Y') rest) = just (ParseTree (parsed-alpha-range-2 (string-append 0 (char-to-string 'Y'))) ::' rest , 2)
len-dec-rewrite {- P51-} ((Id "P51") :: _::_(InputChar 'Z') rest) = just (ParseTree (parsed-alpha-range-2 (string-append 0 (char-to-string 'Z'))) ::' rest , 2)
len-dec-rewrite {- P52-} ((Id "P52") :: _::_(ParseTree (parsed-alpha-range-1 x0)) rest) = just (ParseTree (parsed-alpha-bar-3 (string-append 0 x0)) ::' rest , 2)
len-dec-rewrite {- P53-} ((Id "P53") :: _::_(ParseTree (parsed-alpha-range-2 x0)) rest) = just (ParseTree (parsed-alpha-bar-3 (string-append 0 x0)) ::' rest , 2)
len-dec-rewrite {- P54-} ((Id "P54") :: _::_(ParseTree (parsed-alpha-bar-3 x0)) rest) = just (ParseTree (parsed-alpha (string-append 0 x0)) ::' rest , 2)
len-dec-rewrite {- P55-} ((Id "P55") :: _::_(InputChar '0') rest) = just (ParseTree (parsed-numpunct-range-4 (string-append 0 (char-to-string '0'))) ::' rest , 2)
len-dec-rewrite {- P56-} ((Id "P56") :: _::_(InputChar '1') rest) = just (ParseTree (parsed-numpunct-range-4 (string-append 0 (char-to-string '1'))) ::' rest , 2)
len-dec-rewrite {- P57-} ((Id "P57") :: _::_(InputChar '2') rest) = just (ParseTree (parsed-numpunct-range-4 (string-append 0 (char-to-string '2'))) ::' rest , 2)
len-dec-rewrite {- P58-} ((Id "P58") :: _::_(InputChar '3') rest) = just (ParseTree (parsed-numpunct-range-4 (string-append 0 (char-to-string '3'))) ::' rest , 2)
len-dec-rewrite {- P59-} ((Id "P59") :: _::_(InputChar '4') rest) = just (ParseTree (parsed-numpunct-range-4 (string-append 0 (char-to-string '4'))) ::' rest , 2)
len-dec-rewrite {- P6-} ((Id "P6") :: _::_(InputChar 'g') rest) = just (ParseTree (parsed-alpha-range-1 (string-append 0 (char-to-string 'g'))) ::' rest , 2)
len-dec-rewrite {- P60-} ((Id "P60") :: _::_(InputChar '5') rest) = just (ParseTree (parsed-numpunct-range-4 (string-append 0 (char-to-string '5'))) ::' rest , 2)
len-dec-rewrite {- P61-} ((Id "P61") :: _::_(InputChar '6') rest) = just (ParseTree (parsed-numpunct-range-4 (string-append 0 (char-to-string '6'))) ::' rest , 2)
len-dec-rewrite {- P62-} ((Id "P62") :: _::_(InputChar '7') rest) = just (ParseTree (parsed-numpunct-range-4 (string-append 0 (char-to-string '7'))) ::' rest , 2)
len-dec-rewrite {- P63-} ((Id "P63") :: _::_(InputChar '8') rest) = just (ParseTree (parsed-numpunct-range-4 (string-append 0 (char-to-string '8'))) ::' rest , 2)
len-dec-rewrite {- P64-} ((Id "P64") :: _::_(InputChar '9') rest) = just (ParseTree (parsed-numpunct-range-4 (string-append 0 (char-to-string '9'))) ::' rest , 2)
len-dec-rewrite {- P65-} ((Id "P65") :: _::_(InputChar '\'') rest) = just (ParseTree (parsed-numpunct-bar-5 (string-append 0 (char-to-string '\''))) ::' rest , 2)
len-dec-rewrite {- P66-} ((Id "P66") :: _::_(InputChar '-') rest) = just (ParseTree (parsed-numpunct-bar-5 (string-append 0 (char-to-string '-'))) ::' rest , 2)
len-dec-rewrite {- P67-} ((Id "P67") :: _::_(ParseTree (parsed-numpunct-range-4 x0)) rest) = just (ParseTree (parsed-numpunct-bar-6 (string-append 0 x0)) ::' rest , 2)
len-dec-rewrite {- P68-} ((Id "P68") :: _::_(ParseTree (parsed-numpunct-bar-5 x0)) rest) = just (ParseTree (parsed-numpunct-bar-6 (string-append 0 x0)) ::' rest , 2)
len-dec-rewrite {- P69-} ((Id "P69") :: _::_(ParseTree (parsed-numpunct-bar-6 x0)) rest) = just (ParseTree (parsed-numpunct (string-append 0 x0)) ::' rest , 2)
len-dec-rewrite {- P7-} ((Id "P7") :: _::_(InputChar 'h') rest) = just (ParseTree (parsed-alpha-range-1 (string-append 0 (char-to-string 'h'))) ::' rest , 2)
len-dec-rewrite {- P70-} ((Id "P70") :: _::_(ParseTree (parsed-alpha x0)) rest) = just (ParseTree (parsed-var-bar-7 (string-append 0 x0)) ::' rest , 2)
len-dec-rewrite {- P71-} ((Id "P71") :: _::_(ParseTree (parsed-numpunct x0)) rest) = just (ParseTree (parsed-var-bar-7 (string-append 0 x0)) ::' rest , 2)
len-dec-rewrite {- P73-} ((Id "P73") :: (ParseTree (parsed-var-bar-7 x0)) :: _::_(ParseTree (parsed-var-star-8 x1)) rest) = just (ParseTree (parsed-var-star-8 (string-append 1 x0 x1)) ::' rest , 3)
len-dec-rewrite {- P74-} ((Id "P74") :: (ParseTree (parsed-alpha x0)) :: _::_(ParseTree (parsed-var-star-8 x1)) rest) = just (ParseTree (parsed-var (string-append 1 x0 x1)) ::' rest , 3)
len-dec-rewrite {- P75-} ((Id "P75") :: _::_(ParseTree (parsed-alpha x0)) rest) = just (ParseTree (parsed-kvar-bar-9 (string-append 0 x0)) ::' rest , 2)
len-dec-rewrite {- P76-} ((Id "P76") :: _::_(ParseTree (parsed-numpunct x0)) rest) = just (ParseTree (parsed-kvar-bar-9 (string-append 0 x0)) ::' rest , 2)
len-dec-rewrite {- P78-} ((Id "P78") :: (ParseTree (parsed-kvar-bar-9 x0)) :: _::_(ParseTree (parsed-kvar-star-10 x1)) rest) = just (ParseTree (parsed-kvar-star-10 (string-append 1 x0 x1)) ::' rest , 3)
len-dec-rewrite {- P79-} ((Id "P79") :: (InputChar '𝒌') :: _::_(ParseTree (parsed-kvar-star-10 x0)) rest) = just (ParseTree (parsed-kvar (string-append 1 (char-to-string '𝒌') x0)) ::' rest , 3)
len-dec-rewrite {- P8-} ((Id "P8") :: _::_(InputChar 'i') rest) = just (ParseTree (parsed-alpha-range-1 (string-append 0 (char-to-string 'i'))) ::' rest , 2)
len-dec-rewrite {- P80-} ((Id "P80") :: _::_(InputChar '⇒') rest) = just (ParseTree parsed-anychar-bar-11 ::' rest , 2)
len-dec-rewrite {- P81-} ((Id "P81") :: _::_(InputChar '?') rest) = just (ParseTree parsed-anychar-bar-11 ::' rest , 2)
len-dec-rewrite {- P82-} ((Id "P82") :: _::_(InputChar '}') rest) = just (ParseTree parsed-anychar-bar-12 ::' rest , 2)
len-dec-rewrite {- P83-} ((Id "P83") :: _::_(ParseTree parsed-anychar-bar-11) rest) = just (ParseTree parsed-anychar-bar-12 ::' rest , 2)
len-dec-rewrite {- P84-} ((Id "P84") :: _::_(InputChar '{') rest) = just (ParseTree parsed-anychar-bar-13 ::' rest , 2)
len-dec-rewrite {- P85-} ((Id "P85") :: _::_(ParseTree parsed-anychar-bar-12) rest) = just (ParseTree parsed-anychar-bar-13 ::' rest , 2)
len-dec-rewrite {- P86-} ((Id "P86") :: _::_(InputChar '!') rest) = just (ParseTree parsed-anychar-bar-14 ::' rest , 2)
len-dec-rewrite {- P87-} ((Id "P87") :: _::_(ParseTree parsed-anychar-bar-13) rest) = just (ParseTree parsed-anychar-bar-14 ::' rest , 2)
len-dec-rewrite {- P88-} ((Id "P88") :: _::_(InputChar ',') rest) = just (ParseTree parsed-anychar-bar-15 ::' rest , 2)
len-dec-rewrite {- P89-} ((Id "P89") :: _::_(ParseTree parsed-anychar-bar-14) rest) = just (ParseTree parsed-anychar-bar-15 ::' rest , 2)
len-dec-rewrite {- P9-} ((Id "P9") :: _::_(InputChar 'j') rest) = just (ParseTree (parsed-alpha-range-1 (string-append 0 (char-to-string 'j'))) ::' rest , 2)
len-dec-rewrite {- P90-} ((Id "P90") :: _::_(InputChar ']') rest) = just (ParseTree parsed-anychar-bar-16 ::' rest , 2)
len-dec-rewrite {- P91-} ((Id "P91") :: _::_(ParseTree parsed-anychar-bar-15) rest) = just (ParseTree parsed-anychar-bar-16 ::' rest , 2)
len-dec-rewrite {- P92-} ((Id "P92") :: _::_(InputChar '[') rest) = just (ParseTree parsed-anychar-bar-17 ::' rest , 2)
len-dec-rewrite {- P93-} ((Id "P93") :: _::_(ParseTree parsed-anychar-bar-16) rest) = just (ParseTree parsed-anychar-bar-17 ::' rest , 2)
len-dec-rewrite {- P94-} ((Id "P94") :: _::_(InputChar '.') rest) = just (ParseTree parsed-anychar-bar-18 ::' rest , 2)
len-dec-rewrite {- P95-} ((Id "P95") :: _::_(ParseTree parsed-anychar-bar-17) rest) = just (ParseTree parsed-anychar-bar-18 ::' rest , 2)
len-dec-rewrite {- P96-} ((Id "P96") :: _::_(InputChar ':') rest) = just (ParseTree parsed-anychar-bar-19 ::' rest , 2)
len-dec-rewrite {- P97-} ((Id "P97") :: _::_(ParseTree parsed-anychar-bar-18) rest) = just (ParseTree parsed-anychar-bar-19 ::' rest , 2)
len-dec-rewrite {- P98-} ((Id "P98") :: _::_(InputChar ')') rest) = just (ParseTree parsed-anychar-bar-20 ::' rest , 2)
len-dec-rewrite {- P99-} ((Id "P99") :: _::_(ParseTree parsed-anychar-bar-19) rest) = just (ParseTree parsed-anychar-bar-20 ::' rest , 2)
len-dec-rewrite {- Parens-} ((Id "Parens") :: (ParseTree (parsed-posinfo x0)) :: (InputChar '(') :: (ParseTree parsed-ows) :: (ParseTree (parsed-term x1)) :: (ParseTree parsed-ows) :: (InputChar ')') :: _::_(ParseTree (parsed-posinfo x2)) rest) = just (ParseTree (parsed-lterm (norm-term (Parens x0 x1 x2))) ::' rest , 8)
len-dec-rewrite {- Pi-} ((Id "Pi") :: _::_(InputChar 'Π') rest) = just (ParseTree (parsed-binder (norm-binder Pi)) ::' rest , 2)
len-dec-rewrite {- Rec-} ((Id "Rec") :: (ParseTree (parsed-posinfo x0)) :: (InputChar 'r') :: (InputChar 'e') :: (InputChar 'c') :: (ParseTree parsed-ws) :: (ParseTree (parsed-var x1)) :: (ParseTree (parsed-decls x2)) :: (ParseTree (parsed-indices x3)) :: (ParseTree parsed-ows) :: (InputChar '|') :: (ParseTree (parsed-ctordecls x4)) :: (ParseTree parsed-ows) :: (InputChar '=') :: (ParseTree parsed-ows) :: (ParseTree (parsed-type x5)) :: (ParseTree parsed-ws) :: (InputChar 'w') :: (InputChar 'i') :: (InputChar 't') :: (InputChar 'h') :: (ParseTree (parsed-udefs x6)) :: (ParseTree parsed-ows) :: (InputChar '.') :: _::_(ParseTree (parsed-posinfo x7)) rest) = just (ParseTree (parsed-cmd (norm-cmd (Rec x0 x1 x2 x3 x4 x5 x6 x7))) ::' rest , 25)
len-dec-rewrite {- SomeClass-} ((Id "SomeClass") :: (InputChar ':') :: (ParseTree parsed-ows) :: _::_(ParseTree (parsed-tk x0)) rest) = just (ParseTree (parsed-optClass (norm-optClass (SomeClass x0))) ::' rest , 4)
len-dec-rewrite {- Star-} ((Id "Star") :: (ParseTree (parsed-posinfo x0)) :: _::_(InputChar '★') rest) = just (ParseTree (parsed-kind (norm-kind (Star x0))) ::' rest , 3)
len-dec-rewrite {- TermCmd-} ((Id "TermCmd") :: (ParseTree (parsed-maybeVarEq x0)) :: (ParseTree (parsed-term x1)) :: (ParseTree parsed-ows) :: (InputChar '⇐') :: (ParseTree parsed-ows) :: (ParseTree (parsed-type x2)) :: (ParseTree parsed-ows) :: _::_(InputChar '.') rest) = just (ParseTree (parsed-cmd (norm-cmd (TermCmd x0 x1 x2))) ::' rest , 9)
len-dec-rewrite {- Tkk-} ((Id "Tkk") :: (ParseTree (parsed-kind x0)) :: _::_(Id "Tkk_end") rest) = just (ParseTree (parsed-tk (norm-tk (Tkk x0))) ::' rest , 3)
len-dec-rewrite {- Tkt-} ((Id "Tkt") :: _::_(ParseTree (parsed-type x0)) rest) = just (ParseTree (parsed-tk (norm-tk (Tkt x0))) ::' rest , 2)
len-dec-rewrite {- TpApp-} ((ParseTree (parsed-ltype x0)) :: (ParseTree parsed-ws) :: (InputChar '·') :: (ParseTree parsed-ws) :: _::_(ParseTree (parsed-ltype x1)) rest) = just (ParseTree (parsed-ltype (norm-type (TpApp x0 x1))) ::' rest , 5)
len-dec-rewrite {- TpAppt-} ((ParseTree (parsed-ltype x0)) :: (ParseTree parsed-ws) :: _::_(ParseTree (parsed-lterm x1)) rest) = just (ParseTree (parsed-ltype (norm-type (TpAppt x0 x1))) ::' rest , 3)
len-dec-rewrite {- TpArrow-} ((Id "TpArrow") :: (ParseTree (parsed-ltype x0)) :: (ParseTree parsed-ows) :: (InputChar '→') :: (ParseTree parsed-ows) :: _::_(ParseTree (parsed-type x1)) rest) = just (ParseTree (parsed-type (norm-type (TpArrow x0 x1))) ::' rest , 6)
len-dec-rewrite {- TpEq-} ((Id "TpEq") :: (ParseTree (parsed-lterm x0)) :: (ParseTree parsed-ows) :: (InputChar '≃') :: (ParseTree parsed-ows) :: _::_(ParseTree (parsed-lterm x1)) rest) = just (ParseTree (parsed-ltype (norm-type (TpEq x0 x1))) ::' rest , 6)
len-dec-rewrite {- TpLambda-} ((Id "TpLambda") :: _::_(InputChar 'λ') rest) = just (ParseTree (parsed-binder (norm-binder TpLambda)) ::' rest , 2)
len-dec-rewrite {- TpParens-} ((Id "TpParens") :: (ParseTree (parsed-posinfo x0)) :: (InputChar '(') :: (ParseTree parsed-ows) :: (ParseTree (parsed-type x1)) :: (ParseTree parsed-ows) :: (InputChar ')') :: _::_(ParseTree (parsed-posinfo x2)) rest) = just (ParseTree (parsed-ltype (norm-type (TpParens x0 x1 x2))) ::' rest , 8)
len-dec-rewrite {- TpVar-} ((Id "TpVar") :: (ParseTree (parsed-posinfo x0)) :: _::_(ParseTree (parsed-var x1)) rest) = just (ParseTree (parsed-ltype (norm-type (TpVar x0 x1))) ::' rest , 3)
len-dec-rewrite {- TypeCmd-} ((Id "TypeCmd") :: (ParseTree (parsed-maybeVarEq x0)) :: (ParseTree (parsed-type x1)) :: (ParseTree parsed-ows) :: (InputChar '⇐') :: (ParseTree parsed-ows) :: (ParseTree (parsed-kind x2)) :: (ParseTree parsed-ows) :: _::_(InputChar '.') rest) = just (ParseTree (parsed-cmd (norm-cmd (TypeCmd x0 x1 x2))) ::' rest , 9)
len-dec-rewrite {- Udef-} ((Id "Udef") :: (ParseTree (parsed-var x0)) :: (ParseTree parsed-ows) :: (InputChar '=') :: (ParseTree parsed-ows) :: (ParseTree (parsed-term x1)) :: _::_(Id "Udef_end") rest) = just (ParseTree (parsed-udef (norm-udef (Udef x0 x1))) ::' rest , 7)
len-dec-rewrite {- Udefsne-} ((Id "Udefsne") :: _::_(ParseTree (parsed-udefsne x0)) rest) = just (ParseTree (parsed-udefs (norm-udefs (Udefsne x0))) ::' rest , 2)
len-dec-rewrite {- UdefsneNext-} ((Id "UdefsneNext") :: (ParseTree parsed-ows) :: (ParseTree (parsed-udef x0)) :: (ParseTree parsed-ows) :: (InputChar ',') :: _::_(ParseTree (parsed-udefsne x1)) rest) = just (ParseTree (parsed-udefsne (norm-udefsne (UdefsneNext x0 x1))) ::' rest , 6)
len-dec-rewrite {- UdefsneStart-} ((Id "UdefsneStart") :: (ParseTree parsed-ows) :: _::_(ParseTree (parsed-udef x0)) rest) = just (ParseTree (parsed-udefsne (norm-udefsne (UdefsneStart x0))) ::' rest , 3)
len-dec-rewrite {- Var-} ((Id "Var") :: (ParseTree (parsed-posinfo x0)) :: _::_(ParseTree (parsed-var x1)) rest) = just (ParseTree (parsed-lterm (norm-term (Var x0 x1))) ::' rest , 3)
len-dec-rewrite {- VarEq-} ((Id "VarEq") :: (ParseTree (parsed-var x0)) :: (ParseTree parsed-ows) :: (InputChar '=') :: _::_(ParseTree parsed-ows) rest) = just (ParseTree (parsed-maybeVarEq (norm-maybeVarEq (VarEq x0))) ::' rest , 5)
len-dec-rewrite {- embed-} ((Id "embed") :: _::_(ParseTree (parsed-lterm x0)) rest) = just (ParseTree (parsed-term x0) ::' rest , 2)
len-dec-rewrite {- embed-} ((Id "embed") :: (ParseTree (parsed-ltype x0)) :: _::_(Id "embed_end") rest) = just (ParseTree (parsed-type x0) ::' rest , 3)
len-dec-rewrite {- embed-} ((Id "embed") :: _::_(ParseTree (parsed-lliftingType x0)) rest) = just (ParseTree (parsed-liftingType x0) ::' rest , 2)
len-dec-rewrite {- NoClass-} (_::_(Id "NoClass") rest) = just (ParseTree (parsed-optClass (norm-optClass NoClass)) ::' rest , 1)
len-dec-rewrite {- NoKvarEq-} (_::_(Id "NoKvarEq") rest) = just (ParseTree (parsed-maybeKvarEq (norm-maybeKvarEq NoKvarEq)) ::' rest , 1)
len-dec-rewrite {- NoVarEq-} (_::_(Id "NoVarEq") rest) = just (ParseTree (parsed-maybeVarEq (norm-maybeVarEq NoVarEq)) ::' rest , 1)
len-dec-rewrite {- NotErased-} (_::_(Id "NotErased") rest) = just (ParseTree (parsed-maybeErased (norm-maybeErased NotErased)) ::' rest , 1)
len-dec-rewrite {- P141-} (_::_(Id "P141") rest) = just (ParseTree parsed-comment-star-41 ::' rest , 1)
len-dec-rewrite {- P154-} (_::_(Id "P154") rest) = just (ParseTree parsed-ows-star-46 ::' rest , 1)
len-dec-rewrite {- P72-} (_::_(Id "P72") rest) = just (ParseTree (parsed-var-star-8 empty-string) ::' rest , 1)
len-dec-rewrite {- P77-} (_::_(Id "P77") rest) = just (ParseTree (parsed-kvar-star-10 empty-string) ::' rest , 1)
len-dec-rewrite {- Posinfo-} (_::_(Posinfo n) rest) = just (ParseTree (parsed-posinfo (ℕ-to-string n)) ::' rest , 1)
len-dec-rewrite {- Udefse-} (_::_(Id "Udefse") rest) = just (ParseTree (parsed-udefs (norm-udefs Udefse)) ::' rest , 1)
len-dec-rewrite x = nothing

rrs : rewriteRules
rrs = record { len-dec-rewrite = len-dec-rewrite }
