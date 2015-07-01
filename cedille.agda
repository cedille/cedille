module cedille where

open import lib

open import cedille-types public
----------------------------------------------------------------------------------
-- Run-rewriting rules
----------------------------------------------------------------------------------

data gratr2-nt : Set where
  _ws-plus-59 : gratr2-nt
  _ws : gratr2-nt
  _varone-range-2 : gratr2-nt
  _varone-range-1 : gratr2-nt
  _varone-bar-5 : gratr2-nt
  _varone-bar-4 : gratr2-nt
  _varone-bar-3 : gratr2-nt
  _varone : gratr2-nt
  _var-plus-7 : gratr2-nt
  _var : gratr2-nt
  _type : gratr2-nt
  _tk : gratr2-nt
  _term : gratr2-nt
  _start : gratr2-nt
  _showCtxt : gratr2-nt
  _ows-star-60 : gratr2-nt
  _ows : gratr2-nt
  _opt_eclass : gratr2-nt
  _ltype : gratr2-nt
  _lterm : gratr2-nt
  _lliftingType : gratr2-nt
  _liftingType : gratr2-nt
  _levidence : gratr2-nt
  _kvar-opt-6 : gratr2-nt
  _kvar : gratr2-nt
  _kind : gratr2-nt
  _ip : gratr2-nt
  _index : gratr2-nt
  _evidence : gratr2-nt
  _evar-bar-8 : gratr2-nt
  _evar : gratr2-nt
  _def : gratr2-nt
  _ctorset : gratr2-nt
  _comment-star-55 : gratr2-nt
  _comment : gratr2-nt
  _cmds : gratr2-nt
  _cmd : gratr2-nt
  _class : gratr2-nt
  _castDir : gratr2-nt
  _aws-bar-58 : gratr2-nt
  _aws-bar-57 : gratr2-nt
  _aws-bar-56 : gratr2-nt
  _aws : gratr2-nt
  _anychar-range-9 : gratr2-nt
  _anychar-bar-54 : gratr2-nt
  _anychar-bar-53 : gratr2-nt
  _anychar-bar-52 : gratr2-nt
  _anychar-bar-51 : gratr2-nt
  _anychar-bar-50 : gratr2-nt
  _anychar-bar-49 : gratr2-nt
  _anychar-bar-48 : gratr2-nt
  _anychar-bar-47 : gratr2-nt
  _anychar-bar-46 : gratr2-nt
  _anychar-bar-45 : gratr2-nt
  _anychar-bar-44 : gratr2-nt
  _anychar-bar-43 : gratr2-nt
  _anychar-bar-42 : gratr2-nt
  _anychar-bar-41 : gratr2-nt
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
  _anychar-bar-10 : gratr2-nt
  _anychar : gratr2-nt
  _al : gratr2-nt


gratr2-nt-eq : gratr2-nt → gratr2-nt → 𝔹
gratr2-nt-eq  _ws-plus-59 _ws-plus-59 = tt
gratr2-nt-eq  _ws _ws = tt
gratr2-nt-eq  _varone-range-2 _varone-range-2 = tt
gratr2-nt-eq  _varone-range-1 _varone-range-1 = tt
gratr2-nt-eq  _varone-bar-5 _varone-bar-5 = tt
gratr2-nt-eq  _varone-bar-4 _varone-bar-4 = tt
gratr2-nt-eq  _varone-bar-3 _varone-bar-3 = tt
gratr2-nt-eq  _varone _varone = tt
gratr2-nt-eq  _var-plus-7 _var-plus-7 = tt
gratr2-nt-eq  _var _var = tt
gratr2-nt-eq  _type _type = tt
gratr2-nt-eq  _tk _tk = tt
gratr2-nt-eq  _term _term = tt
gratr2-nt-eq  _start _start = tt
gratr2-nt-eq  _showCtxt _showCtxt = tt
gratr2-nt-eq  _ows-star-60 _ows-star-60 = tt
gratr2-nt-eq  _ows _ows = tt
gratr2-nt-eq  _opt_eclass _opt_eclass = tt
gratr2-nt-eq  _ltype _ltype = tt
gratr2-nt-eq  _lterm _lterm = tt
gratr2-nt-eq  _lliftingType _lliftingType = tt
gratr2-nt-eq  _liftingType _liftingType = tt
gratr2-nt-eq  _levidence _levidence = tt
gratr2-nt-eq  _kvar-opt-6 _kvar-opt-6 = tt
gratr2-nt-eq  _kvar _kvar = tt
gratr2-nt-eq  _kind _kind = tt
gratr2-nt-eq  _ip _ip = tt
gratr2-nt-eq  _index _index = tt
gratr2-nt-eq  _evidence _evidence = tt
gratr2-nt-eq  _evar-bar-8 _evar-bar-8 = tt
gratr2-nt-eq  _evar _evar = tt
gratr2-nt-eq  _def _def = tt
gratr2-nt-eq  _ctorset _ctorset = tt
gratr2-nt-eq  _comment-star-55 _comment-star-55 = tt
gratr2-nt-eq  _comment _comment = tt
gratr2-nt-eq  _cmds _cmds = tt
gratr2-nt-eq  _cmd _cmd = tt
gratr2-nt-eq  _class _class = tt
gratr2-nt-eq  _castDir _castDir = tt
gratr2-nt-eq  _aws-bar-58 _aws-bar-58 = tt
gratr2-nt-eq  _aws-bar-57 _aws-bar-57 = tt
gratr2-nt-eq  _aws-bar-56 _aws-bar-56 = tt
gratr2-nt-eq  _aws _aws = tt
gratr2-nt-eq  _anychar-range-9 _anychar-range-9 = tt
gratr2-nt-eq  _anychar-bar-54 _anychar-bar-54 = tt
gratr2-nt-eq  _anychar-bar-53 _anychar-bar-53 = tt
gratr2-nt-eq  _anychar-bar-52 _anychar-bar-52 = tt
gratr2-nt-eq  _anychar-bar-51 _anychar-bar-51 = tt
gratr2-nt-eq  _anychar-bar-50 _anychar-bar-50 = tt
gratr2-nt-eq  _anychar-bar-49 _anychar-bar-49 = tt
gratr2-nt-eq  _anychar-bar-48 _anychar-bar-48 = tt
gratr2-nt-eq  _anychar-bar-47 _anychar-bar-47 = tt
gratr2-nt-eq  _anychar-bar-46 _anychar-bar-46 = tt
gratr2-nt-eq  _anychar-bar-45 _anychar-bar-45 = tt
gratr2-nt-eq  _anychar-bar-44 _anychar-bar-44 = tt
gratr2-nt-eq  _anychar-bar-43 _anychar-bar-43 = tt
gratr2-nt-eq  _anychar-bar-42 _anychar-bar-42 = tt
gratr2-nt-eq  _anychar-bar-41 _anychar-bar-41 = tt
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
gratr2-nt-eq  _anychar-bar-10 _anychar-bar-10 = tt
gratr2-nt-eq  _anychar _anychar = tt
gratr2-nt-eq  _al _al = tt
gratr2-nt-eq _ _ = ff


open import rtn gratr2-nt


cedille-start : gratr2-nt → 𝕃 gratr2-rule
cedille-start _ws-plus-59 = (just "P222" , nothing , just _ws-plus-59 , inj₁ _aws :: inj₁ _ws-plus-59 :: []) :: (just "P221" , nothing , just _ws-plus-59 , inj₁ _aws :: []) :: []
cedille-start _ws = (just "P223" , nothing , just _ws , inj₁ _ws-plus-59 :: []) :: []
cedille-start _varone-range-2 = (just "P51" , nothing , just _varone-range-2 , inj₂ 'Z' :: []) :: (just "P50" , nothing , just _varone-range-2 , inj₂ 'Y' :: []) :: (just "P49" , nothing , just _varone-range-2 , inj₂ 'X' :: []) :: (just "P48" , nothing , just _varone-range-2 , inj₂ 'W' :: []) :: (just "P47" , nothing , just _varone-range-2 , inj₂ 'V' :: []) :: (just "P46" , nothing , just _varone-range-2 , inj₂ 'U' :: []) :: (just "P45" , nothing , just _varone-range-2 , inj₂ 'T' :: []) :: (just "P44" , nothing , just _varone-range-2 , inj₂ 'S' :: []) :: (just "P43" , nothing , just _varone-range-2 , inj₂ 'R' :: []) :: (just "P42" , nothing , just _varone-range-2 , inj₂ 'Q' :: []) :: (just "P41" , nothing , just _varone-range-2 , inj₂ 'P' :: []) :: (just "P40" , nothing , just _varone-range-2 , inj₂ 'O' :: []) :: (just "P39" , nothing , just _varone-range-2 , inj₂ 'N' :: []) :: (just "P38" , nothing , just _varone-range-2 , inj₂ 'M' :: []) :: (just "P37" , nothing , just _varone-range-2 , inj₂ 'L' :: []) :: (just "P36" , nothing , just _varone-range-2 , inj₂ 'K' :: []) :: (just "P35" , nothing , just _varone-range-2 , inj₂ 'J' :: []) :: (just "P34" , nothing , just _varone-range-2 , inj₂ 'I' :: []) :: (just "P33" , nothing , just _varone-range-2 , inj₂ 'H' :: []) :: (just "P32" , nothing , just _varone-range-2 , inj₂ 'G' :: []) :: (just "P31" , nothing , just _varone-range-2 , inj₂ 'F' :: []) :: (just "P30" , nothing , just _varone-range-2 , inj₂ 'E' :: []) :: (just "P29" , nothing , just _varone-range-2 , inj₂ 'D' :: []) :: (just "P28" , nothing , just _varone-range-2 , inj₂ 'C' :: []) :: (just "P27" , nothing , just _varone-range-2 , inj₂ 'B' :: []) :: (just "P26" , nothing , just _varone-range-2 , inj₂ 'A' :: []) :: []
cedille-start _varone-range-1 = (just "P9" , nothing , just _varone-range-1 , inj₂ 'j' :: []) :: (just "P8" , nothing , just _varone-range-1 , inj₂ 'i' :: []) :: (just "P7" , nothing , just _varone-range-1 , inj₂ 'h' :: []) :: (just "P6" , nothing , just _varone-range-1 , inj₂ 'g' :: []) :: (just "P5" , nothing , just _varone-range-1 , inj₂ 'f' :: []) :: (just "P4" , nothing , just _varone-range-1 , inj₂ 'e' :: []) :: (just "P3" , nothing , just _varone-range-1 , inj₂ 'd' :: []) :: (just "P25" , nothing , just _varone-range-1 , inj₂ 'z' :: []) :: (just "P24" , nothing , just _varone-range-1 , inj₂ 'y' :: []) :: (just "P23" , nothing , just _varone-range-1 , inj₂ 'x' :: []) :: (just "P22" , nothing , just _varone-range-1 , inj₂ 'w' :: []) :: (just "P21" , nothing , just _varone-range-1 , inj₂ 'v' :: []) :: (just "P20" , nothing , just _varone-range-1 , inj₂ 'u' :: []) :: (just "P2" , nothing , just _varone-range-1 , inj₂ 'c' :: []) :: (just "P19" , nothing , just _varone-range-1 , inj₂ 't' :: []) :: (just "P18" , nothing , just _varone-range-1 , inj₂ 's' :: []) :: (just "P17" , nothing , just _varone-range-1 , inj₂ 'r' :: []) :: (just "P16" , nothing , just _varone-range-1 , inj₂ 'q' :: []) :: (just "P15" , nothing , just _varone-range-1 , inj₂ 'p' :: []) :: (just "P14" , nothing , just _varone-range-1 , inj₂ 'o' :: []) :: (just "P13" , nothing , just _varone-range-1 , inj₂ 'n' :: []) :: (just "P12" , nothing , just _varone-range-1 , inj₂ 'm' :: []) :: (just "P11" , nothing , just _varone-range-1 , inj₂ 'l' :: []) :: (just "P10" , nothing , just _varone-range-1 , inj₂ 'k' :: []) :: (just "P1" , nothing , just _varone-range-1 , inj₂ 'b' :: []) :: (just "P0" , nothing , just _varone-range-1 , inj₂ 'a' :: []) :: []
cedille-start _varone-bar-5 = (just "P57" , nothing , just _varone-bar-5 , inj₁ _varone-bar-4 :: []) :: (just "P56" , nothing , just _varone-bar-5 , inj₁ _varone-range-1 :: []) :: []
cedille-start _varone-bar-4 = (just "P55" , nothing , just _varone-bar-4 , inj₁ _varone-bar-3 :: []) :: (just "P54" , nothing , just _varone-bar-4 , inj₁ _varone-range-2 :: []) :: []
cedille-start _varone-bar-3 = (just "P53" , nothing , just _varone-bar-3 , inj₂ '-' :: []) :: (just "P52" , nothing , just _varone-bar-3 , inj₂ '\'' :: []) :: []
cedille-start _varone = (just "P58" , nothing , just _varone , inj₁ _varone-bar-5 :: []) :: []
cedille-start _var-plus-7 = (just "P63" , nothing , just _var-plus-7 , inj₁ _varone :: inj₁ _var-plus-7 :: []) :: (just "P62" , nothing , just _var-plus-7 , inj₁ _varone :: []) :: []
cedille-start _var = (just "P64" , nothing , just _var , inj₁ _var-plus-7 :: []) :: []
cedille-start _type = (just "embed" , just "embed_end" , just _type , inj₁ _ltype :: []) :: (just "TpArrow" , nothing , just _type , inj₁ _ltype :: inj₁ _ows :: inj₂ '→' :: inj₁ _ows :: inj₁ _type :: []) :: (just "Nu" , nothing , just _type , inj₂ 'ν' :: inj₁ _ows :: inj₁ _var :: inj₁ _ows :: inj₂ ':' :: inj₁ _ows :: inj₁ _kind :: inj₁ _ows :: inj₂ '|' :: inj₁ _ows :: inj₁ _ctorset :: inj₁ _ows :: inj₂ '.' :: inj₁ _ows :: inj₁ _type :: []) :: (just "AbsTp2" , nothing , just _type , inj₁ _al :: inj₁ _ows :: inj₁ _var :: inj₁ _ows :: inj₂ ':' :: inj₁ _ows :: inj₁ _tk :: inj₁ _ows :: inj₂ '.' :: inj₁ _ows :: inj₁ _type :: []) :: (just "AbsTp1" , nothing , just _type , inj₁ _ip :: inj₁ _ows :: inj₁ _var :: inj₁ _ows :: inj₂ ':' :: inj₁ _ows :: inj₁ _type :: inj₁ _ows :: inj₂ '.' :: inj₁ _ows :: inj₁ _type :: []) :: []
cedille-start _tk = (just "Tkt" , nothing , just _tk , inj₁ _type :: []) :: (just "Tkk" , just "Tkk_end" , just _tk , inj₁ _kind :: []) :: []
cedille-start _term = (just "embed" , just "embed_end" , just _term , inj₁ _lterm :: []) :: (just "Lam" , nothing , just _term , inj₂ 'λ' :: inj₁ _ows :: inj₁ _var :: inj₁ _ows :: inj₂ '.' :: inj₁ _ows :: inj₁ _term :: []) :: []
cedille-start _start = (just "Cmds" , nothing , just _start , inj₁ _ows :: inj₁ _cmds :: inj₁ _ows :: []) :: []
cedille-start _showCtxt = (just "showCtxtYes" , nothing , just _showCtxt , inj₂ '!' :: []) :: (just "showCtxtNo" , nothing , just _showCtxt , []) :: []
cedille-start _ows-star-60 = (just "P225" , nothing , just _ows-star-60 , inj₁ _aws :: inj₁ _ows-star-60 :: []) :: (just "P224" , nothing , just _ows-star-60 , []) :: []
cedille-start _ows = (just "P226" , nothing , just _ows , inj₁ _ows-star-60 :: []) :: []
cedille-start _opt_eclass = (just "EclassSome" , nothing , just _opt_eclass , inj₁ _ows :: inj₂ ':' :: inj₁ _ows :: inj₁ _evidence :: []) :: (just "EclassNone" , nothing , just _opt_eclass , []) :: []
cedille-start _ltype = (just "U" , nothing , just _ltype , inj₂ '𝓤' :: []) :: (just "TpVar" , nothing , just _ltype , inj₁ _var :: []) :: (just "TpParens" , nothing , just _ltype , inj₂ '(' :: inj₁ _ows :: inj₁ _type :: inj₁ _ows :: inj₂ ')' :: []) :: (just "Lft" , nothing , just _ltype , inj₂ '↑' :: inj₁ _ows :: inj₁ _term :: inj₁ _ows :: inj₂ ':' :: inj₁ _ows :: inj₁ _lliftingType :: []) :: []
cedille-start _lterm = (just "Var" , nothing , just _lterm , inj₁ _var :: []) :: (just "Parens" , nothing , just _lterm , inj₂ '(' :: inj₁ _ows :: inj₁ _term :: inj₁ _ows :: inj₂ ')' :: []) :: []
cedille-start _lliftingType = (just "LiftParens" , nothing , just _lliftingType , inj₂ '(' :: inj₁ _ows :: inj₁ _liftingType :: inj₁ _ows :: inj₂ ')' :: []) :: []
cedille-start _liftingType = (just "embed" , nothing , just _liftingType , inj₁ _lliftingType :: []) :: (just "LiftTpArrow" , nothing , just _liftingType , inj₁ _type :: inj₁ _ows :: inj₂ '→' :: inj₁ _ows :: inj₁ _liftingType :: []) :: (just "LiftStar" , nothing , just _liftingType , inj₂ '☆' :: []) :: (just "LiftPi" , nothing , just _liftingType , inj₂ 'Π' :: inj₁ _ows :: inj₁ _var :: inj₁ _ows :: inj₂ ':' :: inj₁ _ows :: inj₁ _type :: inj₁ _ows :: inj₂ '.' :: inj₁ _ows :: inj₁ _liftingType :: []) :: []
cedille-start _levidence = (just "Sym" , nothing , just _levidence , inj₂ '~' :: inj₁ _ows :: inj₁ _levidence :: []) :: (just "Evar" , nothing , just _levidence , inj₁ _evar :: []) :: (just "Eparens" , nothing , just _levidence , inj₂ '(' :: inj₁ _ows :: inj₁ _evidence :: inj₁ _ows :: inj₂ ')' :: []) :: (just "EholeNamed" , nothing , just _levidence , inj₂ '●' :: inj₁ _showCtxt :: inj₁ _var :: []) :: (just "Ehole" , nothing , just _levidence , inj₂ '●' :: inj₁ _showCtxt :: []) :: (just "Eappt" , nothing , just _levidence , inj₂ '{' :: inj₁ _ows :: inj₁ _levidence :: inj₁ _ws :: inj₁ _term :: inj₁ _ows :: inj₂ '}' :: []) :: (just "Eappk" , nothing , just _levidence , inj₂ '〈' :: inj₁ _ows :: inj₁ _levidence :: inj₁ _ws :: inj₁ _type :: inj₁ _ows :: inj₂ '〉' :: []) :: (just "Check" , nothing , just _levidence , inj₂ '✓' :: []) :: (just "Beta" , nothing , just _levidence , inj₂ 'β' :: []) :: []
cedille-start _kvar-opt-6 = (just "P60" , nothing , just _kvar-opt-6 , []) :: (just "P59" , nothing , just _kvar-opt-6 , inj₁ _var :: []) :: []
cedille-start _kvar = (just "P61" , nothing , just _kvar , inj₂ '𝒌' :: inj₁ _kvar-opt-6 :: []) :: []
cedille-start _kind = (just "Star" , nothing , just _kind , inj₂ '★' :: []) :: (just "KndVar" , nothing , just _kind , inj₁ _kvar :: []) :: (just "KndTpArrow" , nothing , just _kind , inj₁ _ltype :: inj₁ _ows :: inj₂ '→' :: inj₁ _ows :: inj₁ _kind :: []) :: (just "KndPi" , nothing , just _kind , inj₂ 'Π' :: inj₁ _ows :: inj₁ _var :: inj₁ _ows :: inj₂ ':' :: inj₁ _ows :: inj₁ _tk :: inj₁ _ows :: inj₂ '.' :: inj₁ _ows :: inj₁ _kind :: []) :: (just "KndParens" , nothing , just _kind , inj₂ '(' :: inj₁ _ows :: inj₁ _kind :: inj₁ _ows :: inj₂ ')' :: []) :: []
cedille-start _ip = (just "Pi" , nothing , just _ip , inj₂ 'Π' :: []) :: (just "Iota" , nothing , just _ip , inj₂ 'ι' :: []) :: []
cedille-start _index = (just "Two" , nothing , just _index , inj₂ '2' :: []) :: (just "One" , nothing , just _index , inj₂ '1' :: []) :: []
cedille-start _evidence = (just "embed" , just "embed_end" , just _evidence , inj₁ _levidence :: []) :: (just "Xi" , nothing , just _evidence , inj₂ 'ξ' :: inj₁ _ows :: inj₁ _var :: inj₁ _opt_eclass :: inj₁ _ows :: inj₂ '.' :: inj₁ _ows :: inj₁ _evidence :: []) :: (just "Rbeta" , nothing , just _evidence , inj₂ 'r' :: inj₂ 'β' :: inj₁ _ows :: inj₁ _evidence :: inj₁ _ws :: inj₁ _term :: []) :: (just "Pair" , nothing , just _evidence , inj₂ '[' :: inj₁ _ows :: inj₁ _evidence :: inj₁ _ows :: inj₂ ',' :: inj₁ _ows :: inj₁ _evidence :: inj₁ _ows :: inj₂ ']' :: []) :: (just "Eta" , nothing , just _evidence , inj₂ 'η' :: inj₁ _ws :: inj₁ _evidence :: inj₁ _ws :: inj₁ _term :: []) :: (just "Eprint" , nothing , just _evidence , inj₂ '?' :: inj₁ _showCtxt :: inj₁ _ows :: inj₁ _evidence :: []) :: (just "Enu" , nothing , just _evidence , inj₂ 'ν' :: inj₁ _ws :: inj₁ _var :: inj₁ _ows :: inj₂ ',' :: inj₁ _ows :: inj₁ _var :: inj₁ _ows :: inj₂ '.' :: inj₁ _ows :: inj₂ '[' :: inj₁ _ows :: inj₁ _evidence :: inj₁ _ows :: inj₂ ',' :: inj₁ _ows :: inj₁ _evidence :: inj₁ _ows :: inj₂ ',' :: inj₁ _ows :: inj₁ _evidence :: inj₁ _ows :: inj₂ ',' :: inj₁ _ows :: inj₁ _evidence :: inj₁ _ows :: inj₂ ']' :: []) :: (just "Elift" , nothing , just _evidence , inj₂ '↑' :: inj₁ _ows :: inj₁ _var :: inj₁ _ows :: inj₂ '.' :: inj₁ _ows :: inj₁ _evidence :: inj₁ _ows :: inj₂ ':' :: inj₁ _ows :: inj₁ _evidence :: []) :: (just "Elet" , nothing , just _evidence , inj₂ 'δ' :: inj₁ _ws :: inj₁ _def :: inj₁ _ws :: inj₂ '-' :: inj₁ _ws :: inj₁ _evidence :: []) :: (just "Ctora" , nothing , just _evidence , inj₂ 'ζ' :: inj₁ _ws :: inj₁ _var :: []) :: (just "Ctor" , nothing , just _evidence , inj₂ 'ζ' :: inj₁ _ws :: inj₁ _evidence :: inj₁ _ows :: inj₂ ':' :: inj₁ _ows :: inj₁ _type :: []) :: (just "Cast" , nothing , just _evidence , inj₂ 'χ' :: inj₁ _ws :: inj₁ _evidence :: inj₁ _ows :: inj₁ _castDir :: inj₁ _ows :: inj₁ _evidence :: []) :: []
cedille-start _evar-bar-8 = (just "P66" , nothing , just _evar-bar-8 , inj₁ _kvar :: []) :: (just "P65" , nothing , just _evar-bar-8 , inj₁ _var :: []) :: []
cedille-start _evar = (just "P67" , nothing , just _evar , inj₁ _evar-bar-8 :: []) :: []
cedille-start _def = (just "Tdefine" , nothing , just _def , inj₁ _var :: inj₁ _ows :: inj₂ '=' :: inj₁ _ows :: inj₁ _term :: []) :: (just "Kdefine" , nothing , just _def , inj₁ _kvar :: inj₁ _ows :: inj₂ '∷' :: inj₁ _ows :: inj₁ _kind :: inj₁ _ows :: inj₂ '⇐' :: inj₁ _ows :: inj₂ '□' :: inj₁ _ows :: inj₂ '=' :: inj₁ _ows :: inj₁ _evidence :: []) :: (just "Edefine" , nothing , just _def , inj₁ _var :: inj₁ _ows :: inj₂ '∷' :: inj₁ _ows :: inj₁ _class :: inj₁ _ows :: inj₂ '=' :: inj₁ _ows :: inj₁ _evidence :: inj₁ _ows :: inj₂ '⇐' :: inj₁ _ows :: inj₁ _evidence :: []) :: []
cedille-start _ctorset = (just "Empty" , nothing , just _ctorset , inj₂ '·' :: []) :: (just "Add" , nothing , just _ctorset , inj₁ _term :: inj₁ _ows :: inj₂ '∈' :: inj₁ _ows :: inj₁ _type :: inj₁ _ows :: inj₂ ',' :: inj₁ _ows :: inj₁ _ctorset :: []) :: []
cedille-start _comment-star-55 = (just "P212" , nothing , just _comment-star-55 , inj₁ _anychar :: inj₁ _comment-star-55 :: []) :: (just "P211" , nothing , just _comment-star-55 , []) :: []
cedille-start _comment = (just "P213" , nothing , just _comment , inj₂ '%' :: inj₁ _comment-star-55 :: inj₂ '\n' :: []) :: []
cedille-start _cmds = (just "CmdsStart" , nothing , just _cmds , inj₁ _cmd :: []) :: (just "CmdsNext" , nothing , just _cmds , inj₁ _cmd :: inj₁ _ws :: inj₁ _cmds :: []) :: []
cedille-start _cmd = (just "SynthType" , nothing , just _cmd , inj₁ _var :: inj₁ _ows :: inj₂ '∷' :: inj₂ 't' :: inj₂ 'y' :: inj₂ 'p' :: inj₂ 'e' :: inj₁ _ows :: inj₁ _type :: inj₁ _ows :: inj₂ '=' :: inj₁ _ows :: inj₁ _evidence :: inj₁ _ows :: inj₂ '.' :: []) :: (just "SynthTerm" , nothing , just _cmd , inj₁ _var :: inj₁ _ows :: inj₂ '∷' :: inj₁ _ws :: inj₁ _term :: inj₁ _ows :: inj₂ '=' :: inj₁ _ows :: inj₁ _evidence :: inj₁ _ows :: inj₂ '.' :: []) :: (just "Print" , nothing , just _cmd , inj₂ 'p' :: inj₂ 'r' :: inj₂ 'i' :: inj₂ 'n' :: inj₂ 't' :: inj₁ _ws :: inj₁ _var :: inj₁ _ows :: inj₂ '.' :: []) :: (just "Normalize" , nothing , just _cmd , inj₂ 'n' :: inj₂ 'o' :: inj₂ 'r' :: inj₂ 'm' :: inj₁ _ws :: inj₁ _term :: inj₁ _ows :: inj₂ '.' :: []) :: (just "Kcheck" , nothing , just _cmd , inj₁ _kind :: inj₁ _ows :: inj₂ '⇐' :: inj₁ _ows :: inj₂ '□' :: inj₁ _ows :: inj₂ 'b' :: inj₂ 'y' :: inj₁ _ows :: inj₁ _evidence :: inj₁ _ows :: inj₂ '.' :: []) :: (just "Echeck" , nothing , just _cmd , inj₁ _class :: inj₁ _ows :: inj₂ 'b' :: inj₂ 'y' :: inj₁ _ows :: inj₁ _evidence :: inj₁ _ows :: inj₂ '⇐' :: inj₁ _ows :: inj₁ _evidence :: inj₁ _ows :: inj₂ '.' :: []) :: (just "DefCmd" , nothing , just _cmd , inj₁ _def :: inj₁ _ows :: inj₂ '.' :: []) :: []
cedille-start _class = (just "Tp" , nothing , just _class , inj₁ _term :: inj₁ _ows :: inj₂ '⇐' :: inj₁ _ows :: inj₁ _type :: []) :: (just "Knd" , just "Knd_end" , just _class , inj₁ _type :: inj₁ _ows :: inj₂ '⇐' :: inj₁ _ows :: inj₁ _kind :: []) :: []
cedille-start _castDir = (just "synthCast" , nothing , just _castDir , inj₂ '⇒' :: []) :: (just "checkCast" , nothing , just _castDir , inj₂ '⇐' :: []) :: []
cedille-start _aws-bar-58 = (just "P219" , nothing , just _aws-bar-58 , inj₁ _aws-bar-57 :: []) :: (just "P218" , nothing , just _aws-bar-58 , inj₂ '\n' :: []) :: []
cedille-start _aws-bar-57 = (just "P217" , nothing , just _aws-bar-57 , inj₁ _aws-bar-56 :: []) :: (just "P216" , nothing , just _aws-bar-57 , inj₂ '\t' :: []) :: []
cedille-start _aws-bar-56 = (just "P215" , nothing , just _aws-bar-56 , inj₁ _comment :: []) :: (just "P214" , nothing , just _aws-bar-56 , inj₂ ' ' :: []) :: []
cedille-start _aws = (just "P220" , nothing , just _aws , inj₁ _aws-bar-58 :: []) :: []
cedille-start _anychar-range-9 = (just "P99" , nothing , just _anychar-range-9 , inj₂ 'f' :: []) :: (just "P98" , nothing , just _anychar-range-9 , inj₂ 'e' :: []) :: (just "P97" , nothing , just _anychar-range-9 , inj₂ 'd' :: []) :: (just "P96" , nothing , just _anychar-range-9 , inj₂ 'c' :: []) :: (just "P95" , nothing , just _anychar-range-9 , inj₂ 'b' :: []) :: (just "P94" , nothing , just _anychar-range-9 , inj₂ 'a' :: []) :: (just "P93" , nothing , just _anychar-range-9 , inj₂ 'Z' :: []) :: (just "P92" , nothing , just _anychar-range-9 , inj₂ 'Y' :: []) :: (just "P91" , nothing , just _anychar-range-9 , inj₂ 'X' :: []) :: (just "P90" , nothing , just _anychar-range-9 , inj₂ 'W' :: []) :: (just "P89" , nothing , just _anychar-range-9 , inj₂ 'V' :: []) :: (just "P88" , nothing , just _anychar-range-9 , inj₂ 'U' :: []) :: (just "P87" , nothing , just _anychar-range-9 , inj₂ 'T' :: []) :: (just "P86" , nothing , just _anychar-range-9 , inj₂ 'S' :: []) :: (just "P85" , nothing , just _anychar-range-9 , inj₂ 'R' :: []) :: (just "P84" , nothing , just _anychar-range-9 , inj₂ 'Q' :: []) :: (just "P83" , nothing , just _anychar-range-9 , inj₂ 'P' :: []) :: (just "P82" , nothing , just _anychar-range-9 , inj₂ 'O' :: []) :: (just "P81" , nothing , just _anychar-range-9 , inj₂ 'N' :: []) :: (just "P80" , nothing , just _anychar-range-9 , inj₂ 'M' :: []) :: (just "P79" , nothing , just _anychar-range-9 , inj₂ 'L' :: []) :: (just "P78" , nothing , just _anychar-range-9 , inj₂ 'K' :: []) :: (just "P77" , nothing , just _anychar-range-9 , inj₂ 'J' :: []) :: (just "P76" , nothing , just _anychar-range-9 , inj₂ 'I' :: []) :: (just "P75" , nothing , just _anychar-range-9 , inj₂ 'H' :: []) :: (just "P74" , nothing , just _anychar-range-9 , inj₂ 'G' :: []) :: (just "P73" , nothing , just _anychar-range-9 , inj₂ 'F' :: []) :: (just "P72" , nothing , just _anychar-range-9 , inj₂ 'E' :: []) :: (just "P71" , nothing , just _anychar-range-9 , inj₂ 'D' :: []) :: (just "P70" , nothing , just _anychar-range-9 , inj₂ 'C' :: []) :: (just "P69" , nothing , just _anychar-range-9 , inj₂ 'B' :: []) :: (just "P68" , nothing , just _anychar-range-9 , inj₂ 'A' :: []) :: (just "P119" , nothing , just _anychar-range-9 , inj₂ 'z' :: []) :: (just "P118" , nothing , just _anychar-range-9 , inj₂ 'y' :: []) :: (just "P117" , nothing , just _anychar-range-9 , inj₂ 'x' :: []) :: (just "P116" , nothing , just _anychar-range-9 , inj₂ 'w' :: []) :: (just "P115" , nothing , just _anychar-range-9 , inj₂ 'v' :: []) :: (just "P114" , nothing , just _anychar-range-9 , inj₂ 'u' :: []) :: (just "P113" , nothing , just _anychar-range-9 , inj₂ 't' :: []) :: (just "P112" , nothing , just _anychar-range-9 , inj₂ 's' :: []) :: (just "P111" , nothing , just _anychar-range-9 , inj₂ 'r' :: []) :: (just "P110" , nothing , just _anychar-range-9 , inj₂ 'q' :: []) :: (just "P109" , nothing , just _anychar-range-9 , inj₂ 'p' :: []) :: (just "P108" , nothing , just _anychar-range-9 , inj₂ 'o' :: []) :: (just "P107" , nothing , just _anychar-range-9 , inj₂ 'n' :: []) :: (just "P106" , nothing , just _anychar-range-9 , inj₂ 'm' :: []) :: (just "P105" , nothing , just _anychar-range-9 , inj₂ 'l' :: []) :: (just "P104" , nothing , just _anychar-range-9 , inj₂ 'k' :: []) :: (just "P103" , nothing , just _anychar-range-9 , inj₂ 'j' :: []) :: (just "P102" , nothing , just _anychar-range-9 , inj₂ 'i' :: []) :: (just "P101" , nothing , just _anychar-range-9 , inj₂ 'h' :: []) :: (just "P100" , nothing , just _anychar-range-9 , inj₂ 'g' :: []) :: []
cedille-start _anychar-bar-54 = (just "P209" , nothing , just _anychar-bar-54 , inj₁ _anychar-bar-53 :: []) :: (just "P208" , nothing , just _anychar-bar-54 , inj₁ _anychar-range-9 :: []) :: []
cedille-start _anychar-bar-53 = (just "P207" , nothing , just _anychar-bar-53 , inj₁ _anychar-bar-52 :: []) :: (just "P206" , nothing , just _anychar-bar-53 , inj₂ '\t' :: []) :: []
cedille-start _anychar-bar-52 = (just "P205" , nothing , just _anychar-bar-52 , inj₁ _anychar-bar-51 :: []) :: (just "P204" , nothing , just _anychar-bar-52 , inj₂ ' ' :: []) :: []
cedille-start _anychar-bar-51 = (just "P203" , nothing , just _anychar-bar-51 , inj₁ _anychar-bar-50 :: []) :: (just "P202" , nothing , just _anychar-bar-51 , inj₂ '𝒌' :: []) :: []
cedille-start _anychar-bar-50 = (just "P201" , nothing , just _anychar-bar-50 , inj₁ _anychar-bar-49 :: []) :: (just "P200" , nothing , just _anychar-bar-50 , inj₂ '%' :: []) :: []
cedille-start _anychar-bar-49 = (just "P199" , nothing , just _anychar-bar-49 , inj₁ _anychar-bar-48 :: []) :: (just "P198" , nothing , just _anychar-bar-49 , inj₂ '1' :: []) :: []
cedille-start _anychar-bar-48 = (just "P197" , nothing , just _anychar-bar-48 , inj₁ _anychar-bar-47 :: []) :: (just "P196" , nothing , just _anychar-bar-48 , inj₂ '2' :: []) :: []
cedille-start _anychar-bar-47 = (just "P195" , nothing , just _anychar-bar-47 , inj₁ _anychar-bar-46 :: []) :: (just "P194" , nothing , just _anychar-bar-47 , inj₂ '\'' :: []) :: []
cedille-start _anychar-bar-46 = (just "P193" , nothing , just _anychar-bar-46 , inj₁ _anychar-bar-45 :: []) :: (just "P192" , nothing , just _anychar-bar-46 , inj₂ '∷' :: []) :: []
cedille-start _anychar-bar-45 = (just "P191" , nothing , just _anychar-bar-45 , inj₁ _anychar-bar-44 :: []) :: (just "P190" , nothing , just _anychar-bar-45 , inj₂ '✓' :: []) :: []
cedille-start _anychar-bar-44 = (just "P189" , nothing , just _anychar-bar-44 , inj₁ _anychar-bar-43 :: []) :: (just "P188" , nothing , just _anychar-bar-44 , inj₂ '□' :: []) :: []
cedille-start _anychar-bar-43 = (just "P187" , nothing , just _anychar-bar-43 , inj₁ _anychar-bar-42 :: []) :: (just "P186" , nothing , just _anychar-bar-43 , inj₂ 'Π' :: []) :: []
cedille-start _anychar-bar-42 = (just "P185" , nothing , just _anychar-bar-42 , inj₁ _anychar-bar-41 :: []) :: (just "P184" , nothing , just _anychar-bar-42 , inj₂ 'ι' :: []) :: []
cedille-start _anychar-bar-41 = (just "P183" , nothing , just _anychar-bar-41 , inj₁ _anychar-bar-40 :: []) :: (just "P182" , nothing , just _anychar-bar-41 , inj₂ 'λ' :: []) :: []
cedille-start _anychar-bar-40 = (just "P181" , nothing , just _anychar-bar-40 , inj₁ _anychar-bar-39 :: []) :: (just "P180" , nothing , just _anychar-bar-40 , inj₂ '∀' :: []) :: []
cedille-start _anychar-bar-39 = (just "P179" , nothing , just _anychar-bar-39 , inj₁ _anychar-bar-38 :: []) :: (just "P178" , nothing , just _anychar-bar-39 , inj₂ 'π' :: []) :: []
cedille-start _anychar-bar-38 = (just "P177" , nothing , just _anychar-bar-38 , inj₁ _anychar-bar-37 :: []) :: (just "P176" , nothing , just _anychar-bar-38 , inj₂ '★' :: []) :: []
cedille-start _anychar-bar-37 = (just "P175" , nothing , just _anychar-bar-37 , inj₁ _anychar-bar-36 :: []) :: (just "P174" , nothing , just _anychar-bar-37 , inj₂ '☆' :: []) :: []
cedille-start _anychar-bar-36 = (just "P173" , nothing , just _anychar-bar-36 , inj₁ _anychar-bar-35 :: []) :: (just "P172" , nothing , just _anychar-bar-36 , inj₂ '·' :: []) :: []
cedille-start _anychar-bar-35 = (just "P171" , nothing , just _anychar-bar-35 , inj₁ _anychar-bar-34 :: []) :: (just "P170" , nothing , just _anychar-bar-35 , inj₂ 'ξ' :: []) :: []
cedille-start _anychar-bar-34 = (just "P169" , nothing , just _anychar-bar-34 , inj₁ _anychar-bar-33 :: []) :: (just "P168" , nothing , just _anychar-bar-34 , inj₂ '⇐' :: []) :: []
cedille-start _anychar-bar-33 = (just "P167" , nothing , just _anychar-bar-33 , inj₁ _anychar-bar-32 :: []) :: (just "P166" , nothing , just _anychar-bar-33 , inj₂ '∈' :: []) :: []
cedille-start _anychar-bar-32 = (just "P165" , nothing , just _anychar-bar-32 , inj₁ _anychar-bar-31 :: []) :: (just "P164" , nothing , just _anychar-bar-32 , inj₂ 'ν' :: []) :: []
cedille-start _anychar-bar-31 = (just "P163" , nothing , just _anychar-bar-31 , inj₁ _anychar-bar-30 :: []) :: (just "P162" , nothing , just _anychar-bar-31 , inj₂ '→' :: []) :: []
cedille-start _anychar-bar-30 = (just "P161" , nothing , just _anychar-bar-30 , inj₁ _anychar-bar-29 :: []) :: (just "P160" , nothing , just _anychar-bar-30 , inj₂ '↑' :: []) :: []
cedille-start _anychar-bar-29 = (just "P159" , nothing , just _anychar-bar-29 , inj₁ _anychar-bar-28 :: []) :: (just "P158" , nothing , just _anychar-bar-29 , inj₂ '𝓤' :: []) :: []
cedille-start _anychar-bar-28 = (just "P157" , nothing , just _anychar-bar-28 , inj₁ _anychar-bar-27 :: []) :: (just "P156" , nothing , just _anychar-bar-28 , inj₂ '●' :: []) :: []
cedille-start _anychar-bar-27 = (just "P155" , nothing , just _anychar-bar-27 , inj₁ _anychar-bar-26 :: []) :: (just "P154" , nothing , just _anychar-bar-27 , inj₂ '(' :: []) :: []
cedille-start _anychar-bar-26 = (just "P153" , nothing , just _anychar-bar-26 , inj₁ _anychar-bar-25 :: []) :: (just "P152" , nothing , just _anychar-bar-26 , inj₂ ')' :: []) :: []
cedille-start _anychar-bar-25 = (just "P151" , nothing , just _anychar-bar-25 , inj₁ _anychar-bar-24 :: []) :: (just "P150" , nothing , just _anychar-bar-25 , inj₂ ':' :: []) :: []
cedille-start _anychar-bar-24 = (just "P149" , nothing , just _anychar-bar-24 , inj₁ _anychar-bar-23 :: []) :: (just "P148" , nothing , just _anychar-bar-24 , inj₂ '.' :: []) :: []
cedille-start _anychar-bar-23 = (just "P147" , nothing , just _anychar-bar-23 , inj₁ _anychar-bar-22 :: []) :: (just "P146" , nothing , just _anychar-bar-23 , inj₂ 'χ' :: []) :: []
cedille-start _anychar-bar-22 = (just "P145" , nothing , just _anychar-bar-22 , inj₁ _anychar-bar-21 :: []) :: (just "P144" , nothing , just _anychar-bar-22 , inj₂ 'β' :: []) :: []
cedille-start _anychar-bar-21 = (just "P143" , nothing , just _anychar-bar-21 , inj₁ _anychar-bar-20 :: []) :: (just "P142" , nothing , just _anychar-bar-21 , inj₂ 'δ' :: []) :: []
cedille-start _anychar-bar-20 = (just "P141" , nothing , just _anychar-bar-20 , inj₁ _anychar-bar-19 :: []) :: (just "P140" , nothing , just _anychar-bar-20 , inj₂ 'ζ' :: []) :: []
cedille-start _anychar-bar-19 = (just "P139" , nothing , just _anychar-bar-19 , inj₁ _anychar-bar-18 :: []) :: (just "P138" , nothing , just _anychar-bar-19 , inj₂ '[' :: []) :: []
cedille-start _anychar-bar-18 = (just "P137" , nothing , just _anychar-bar-18 , inj₁ _anychar-bar-17 :: []) :: (just "P136" , nothing , just _anychar-bar-18 , inj₂ ']' :: []) :: []
cedille-start _anychar-bar-17 = (just "P135" , nothing , just _anychar-bar-17 , inj₁ _anychar-bar-16 :: []) :: (just "P134" , nothing , just _anychar-bar-17 , inj₂ ',' :: []) :: []
cedille-start _anychar-bar-16 = (just "P133" , nothing , just _anychar-bar-16 , inj₁ _anychar-bar-15 :: []) :: (just "P132" , nothing , just _anychar-bar-16 , inj₂ '!' :: []) :: []
cedille-start _anychar-bar-15 = (just "P131" , nothing , just _anychar-bar-15 , inj₁ _anychar-bar-14 :: []) :: (just "P130" , nothing , just _anychar-bar-15 , inj₂ '-' :: []) :: []
cedille-start _anychar-bar-14 = (just "P129" , nothing , just _anychar-bar-14 , inj₁ _anychar-bar-13 :: []) :: (just "P128" , nothing , just _anychar-bar-14 , inj₂ '{' :: []) :: []
cedille-start _anychar-bar-13 = (just "P127" , nothing , just _anychar-bar-13 , inj₁ _anychar-bar-12 :: []) :: (just "P126" , nothing , just _anychar-bar-13 , inj₂ '}' :: []) :: []
cedille-start _anychar-bar-12 = (just "P125" , nothing , just _anychar-bar-12 , inj₁ _anychar-bar-11 :: []) :: (just "P124" , nothing , just _anychar-bar-12 , inj₂ '⇒' :: []) :: []
cedille-start _anychar-bar-11 = (just "P123" , nothing , just _anychar-bar-11 , inj₁ _anychar-bar-10 :: []) :: (just "P122" , nothing , just _anychar-bar-11 , inj₂ '?' :: []) :: []
cedille-start _anychar-bar-10 = (just "P121" , nothing , just _anychar-bar-10 , inj₂ 'η' :: []) :: (just "P120" , nothing , just _anychar-bar-10 , inj₂ '~' :: []) :: []
cedille-start _anychar = (just "P210" , nothing , just _anychar , inj₁ _anychar-bar-54 :: []) :: []
cedille-start _al = (just "Lambda" , nothing , just _al , inj₂ 'λ' :: []) :: (just "All" , nothing , just _al , inj₂ '∀' :: []) :: []


cedille-return : maybe gratr2-nt → 𝕃 gratr2-rule
cedille-return (just _ltype) = (nothing , just "TpAppt_end" , just _ltype , inj₁ _ws :: inj₁ _lterm :: []) :: (nothing , nothing , just _ltype , inj₁ _ws :: inj₂ '·' :: inj₁ _ws :: inj₁ _ltype :: []) :: []
cedille-return (just _lterm) = (nothing , nothing , just _lterm , inj₁ _ws :: inj₁ _lterm :: []) :: []
cedille-return (just _liftingType) = (nothing , nothing , just _liftingType , inj₁ _ows :: inj₂ '→' :: inj₁ _ows :: inj₁ _liftingType :: []) :: []
cedille-return (just _levidence) = (nothing , nothing , just _levidence , inj₁ _ows :: inj₂ '·' :: inj₁ _ows :: inj₁ _levidence :: []) :: (nothing , nothing , just _levidence , inj₁ _ows :: inj₂ '.' :: inj₁ _ows :: inj₁ _index :: []) :: (nothing , nothing , just _levidence , inj₁ _ows :: inj₂ '⇒' :: inj₁ _ows :: inj₁ _levidence :: []) :: (nothing , nothing , just _levidence , inj₁ _ws :: inj₁ _levidence :: []) :: []
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
len-dec-rewrite {- AbsTp1-} ((Id "AbsTp1") :: (ParseTree (parsed-ip x0)) :: (ParseTree parsed-ows) :: (ParseTree (parsed-var x1)) :: (ParseTree parsed-ows) :: (InputChar ':') :: (ParseTree parsed-ows) :: (ParseTree (parsed-type x2)) :: (ParseTree parsed-ows) :: (InputChar '.') :: (ParseTree parsed-ows) :: _::_(ParseTree (parsed-type x3)) rest) = just (ParseTree (parsed-type (norm-type (AbsTp1 x0 x1 x2 x3))) ::' rest , 12)
len-dec-rewrite {- AbsTp2-} ((Id "AbsTp2") :: (ParseTree (parsed-al x0)) :: (ParseTree parsed-ows) :: (ParseTree (parsed-var x1)) :: (ParseTree parsed-ows) :: (InputChar ':') :: (ParseTree parsed-ows) :: (ParseTree (parsed-tk x2)) :: (ParseTree parsed-ows) :: (InputChar '.') :: (ParseTree parsed-ows) :: _::_(ParseTree (parsed-type x3)) rest) = just (ParseTree (parsed-type (norm-type (AbsTp2 x0 x1 x2 x3))) ::' rest , 12)
len-dec-rewrite {- Add-} ((Id "Add") :: (ParseTree (parsed-term x0)) :: (ParseTree parsed-ows) :: (InputChar '∈') :: (ParseTree parsed-ows) :: (ParseTree (parsed-type x1)) :: (ParseTree parsed-ows) :: (InputChar ',') :: (ParseTree parsed-ows) :: _::_(ParseTree (parsed-ctorset x2)) rest) = just (ParseTree (parsed-ctorset (norm-ctorset (Add x0 x1 x2))) ::' rest , 10)
len-dec-rewrite {- All-} ((Id "All") :: _::_(InputChar '∀') rest) = just (ParseTree (parsed-al (norm-al All)) ::' rest , 2)
len-dec-rewrite {- App-} ((ParseTree (parsed-lterm x0)) :: (ParseTree parsed-ws) :: _::_(ParseTree (parsed-lterm x1)) rest) = just (ParseTree (parsed-lterm (norm-term (App x0 x1))) ::' rest , 3)
len-dec-rewrite {- Beta-} ((Id "Beta") :: _::_(InputChar 'β') rest) = just (ParseTree (parsed-levidence (norm-evidence Beta)) ::' rest , 2)
len-dec-rewrite {- Cast-} ((Id "Cast") :: (InputChar 'χ') :: (ParseTree parsed-ws) :: (ParseTree (parsed-evidence x0)) :: (ParseTree parsed-ows) :: (ParseTree (parsed-castDir x1)) :: (ParseTree parsed-ows) :: _::_(ParseTree (parsed-evidence x2)) rest) = just (ParseTree (parsed-evidence (norm-evidence (Cast x0 x1 x2))) ::' rest , 8)
len-dec-rewrite {- Check-} ((Id "Check") :: _::_(InputChar '✓') rest) = just (ParseTree (parsed-levidence (norm-evidence Check)) ::' rest , 2)
len-dec-rewrite {- Cmds-} ((Id "Cmds") :: (ParseTree parsed-ows) :: (ParseTree (parsed-cmds x0)) :: _::_(ParseTree parsed-ows) rest) = just (ParseTree (parsed-start (norm-start (Cmds x0))) ::' rest , 4)
len-dec-rewrite {- CmdsNext-} ((Id "CmdsNext") :: (ParseTree (parsed-cmd x0)) :: (ParseTree parsed-ws) :: _::_(ParseTree (parsed-cmds x1)) rest) = just (ParseTree (parsed-cmds (norm-cmds (CmdsNext x0 x1))) ::' rest , 4)
len-dec-rewrite {- CmdsStart-} ((Id "CmdsStart") :: _::_(ParseTree (parsed-cmd x0)) rest) = just (ParseTree (parsed-cmds (norm-cmds (CmdsStart x0))) ::' rest , 2)
len-dec-rewrite {- Ctor-} ((Id "Ctor") :: (InputChar 'ζ') :: (ParseTree parsed-ws) :: (ParseTree (parsed-evidence x0)) :: (ParseTree parsed-ows) :: (InputChar ':') :: (ParseTree parsed-ows) :: _::_(ParseTree (parsed-type x1)) rest) = just (ParseTree (parsed-evidence (norm-evidence (Ctor x0 x1))) ::' rest , 8)
len-dec-rewrite {- Ctora-} ((Id "Ctora") :: (InputChar 'ζ') :: (ParseTree parsed-ws) :: _::_(ParseTree (parsed-var x0)) rest) = just (ParseTree (parsed-evidence (norm-evidence (Ctora x0))) ::' rest , 4)
len-dec-rewrite {- DefCmd-} ((Id "DefCmd") :: (ParseTree (parsed-def x0)) :: (ParseTree parsed-ows) :: _::_(InputChar '.') rest) = just (ParseTree (parsed-cmd (norm-cmd (DefCmd x0))) ::' rest , 4)
len-dec-rewrite {- Eapp-} ((ParseTree (parsed-levidence x0)) :: (ParseTree parsed-ws) :: _::_(ParseTree (parsed-levidence x1)) rest) = just (ParseTree (parsed-levidence (norm-evidence (Eapp x0 x1))) ::' rest , 3)
len-dec-rewrite {- Eappk-} ((Id "Eappk") :: (InputChar '〈') :: (ParseTree parsed-ows) :: (ParseTree (parsed-levidence x0)) :: (ParseTree parsed-ws) :: (ParseTree (parsed-type x1)) :: (ParseTree parsed-ows) :: _::_(InputChar '〉') rest) = just (ParseTree (parsed-levidence (norm-evidence (Eappk x0 x1))) ::' rest , 8)
len-dec-rewrite {- Eappt-} ((Id "Eappt") :: (InputChar '{') :: (ParseTree parsed-ows) :: (ParseTree (parsed-levidence x0)) :: (ParseTree parsed-ws) :: (ParseTree (parsed-term x1)) :: (ParseTree parsed-ows) :: _::_(InputChar '}') rest) = just (ParseTree (parsed-levidence (norm-evidence (Eappt x0 x1))) ::' rest , 8)
len-dec-rewrite {- Earrow-} ((ParseTree (parsed-levidence x0)) :: (ParseTree parsed-ows) :: (InputChar '⇒') :: (ParseTree parsed-ows) :: _::_(ParseTree (parsed-levidence x1)) rest) = just (ParseTree (parsed-levidence (norm-evidence (Earrow x0 x1))) ::' rest , 5)
len-dec-rewrite {- Echeck-} ((Id "Echeck") :: (ParseTree (parsed-class x0)) :: (ParseTree parsed-ows) :: (InputChar 'b') :: (InputChar 'y') :: (ParseTree parsed-ows) :: (ParseTree (parsed-evidence x1)) :: (ParseTree parsed-ows) :: (InputChar '⇐') :: (ParseTree parsed-ows) :: (ParseTree (parsed-evidence x2)) :: (ParseTree parsed-ows) :: _::_(InputChar '.') rest) = just (ParseTree (parsed-cmd (norm-cmd (Echeck x0 x1 x2))) ::' rest , 13)
len-dec-rewrite {- EclassSome-} ((Id "EclassSome") :: (ParseTree parsed-ows) :: (InputChar ':') :: (ParseTree parsed-ows) :: _::_(ParseTree (parsed-evidence x0)) rest) = just (ParseTree (parsed-opt_eclass (norm-opt_eclass (EclassSome x0))) ::' rest , 5)
len-dec-rewrite {- Edefine-} ((Id "Edefine") :: (ParseTree (parsed-var x0)) :: (ParseTree parsed-ows) :: (InputChar '∷') :: (ParseTree parsed-ows) :: (ParseTree (parsed-class x1)) :: (ParseTree parsed-ows) :: (InputChar '=') :: (ParseTree parsed-ows) :: (ParseTree (parsed-evidence x2)) :: (ParseTree parsed-ows) :: (InputChar '⇐') :: (ParseTree parsed-ows) :: _::_(ParseTree (parsed-evidence x3)) rest) = just (ParseTree (parsed-def (norm-def (Edefine x0 x1 x2 x3))) ::' rest , 14)
len-dec-rewrite {- Ehole-} ((Id "Ehole") :: (InputChar '●') :: _::_(ParseTree (parsed-showCtxt x0)) rest) = just (ParseTree (parsed-levidence (norm-evidence (Ehole x0))) ::' rest , 3)
len-dec-rewrite {- EholeNamed-} ((Id "EholeNamed") :: (InputChar '●') :: (ParseTree (parsed-showCtxt x0)) :: _::_(ParseTree (parsed-var x1)) rest) = just (ParseTree (parsed-levidence (norm-evidence (EholeNamed x0 x1))) ::' rest , 4)
len-dec-rewrite {- Elet-} ((Id "Elet") :: (InputChar 'δ') :: (ParseTree parsed-ws) :: (ParseTree (parsed-def x0)) :: (ParseTree parsed-ws) :: (InputChar '-') :: (ParseTree parsed-ws) :: _::_(ParseTree (parsed-evidence x1)) rest) = just (ParseTree (parsed-evidence (norm-evidence (Elet x0 x1))) ::' rest , 8)
len-dec-rewrite {- Elift-} ((Id "Elift") :: (InputChar '↑') :: (ParseTree parsed-ows) :: (ParseTree (parsed-var x0)) :: (ParseTree parsed-ows) :: (InputChar '.') :: (ParseTree parsed-ows) :: (ParseTree (parsed-evidence x1)) :: (ParseTree parsed-ows) :: (InputChar ':') :: (ParseTree parsed-ows) :: _::_(ParseTree (parsed-evidence x2)) rest) = just (ParseTree (parsed-evidence (norm-evidence (Elift x0 x1 x2))) ::' rest , 12)
len-dec-rewrite {- Empty-} ((Id "Empty") :: _::_(InputChar '·') rest) = just (ParseTree (parsed-ctorset (norm-ctorset Empty)) ::' rest , 2)
len-dec-rewrite {- Enu-} ((Id "Enu") :: (InputChar 'ν') :: (ParseTree parsed-ws) :: (ParseTree (parsed-var x0)) :: (ParseTree parsed-ows) :: (InputChar ',') :: (ParseTree parsed-ows) :: (ParseTree (parsed-var x1)) :: (ParseTree parsed-ows) :: (InputChar '.') :: (ParseTree parsed-ows) :: (InputChar '[') :: (ParseTree parsed-ows) :: (ParseTree (parsed-evidence x2)) :: (ParseTree parsed-ows) :: (InputChar ',') :: (ParseTree parsed-ows) :: (ParseTree (parsed-evidence x3)) :: (ParseTree parsed-ows) :: (InputChar ',') :: (ParseTree parsed-ows) :: (ParseTree (parsed-evidence x4)) :: (ParseTree parsed-ows) :: (InputChar ',') :: (ParseTree parsed-ows) :: (ParseTree (parsed-evidence x5)) :: (ParseTree parsed-ows) :: _::_(InputChar ']') rest) = just (ParseTree (parsed-evidence (norm-evidence (Enu x0 x1 x2 x3 x4 x5))) ::' rest , 28)
len-dec-rewrite {- Eparens-} ((Id "Eparens") :: (InputChar '(') :: (ParseTree parsed-ows) :: (ParseTree (parsed-evidence x0)) :: (ParseTree parsed-ows) :: _::_(InputChar ')') rest) = just (ParseTree (parsed-levidence (norm-evidence (Eparens x0))) ::' rest , 6)
len-dec-rewrite {- Eprint-} ((Id "Eprint") :: (InputChar '?') :: (ParseTree (parsed-showCtxt x0)) :: (ParseTree parsed-ows) :: _::_(ParseTree (parsed-evidence x1)) rest) = just (ParseTree (parsed-evidence (norm-evidence (Eprint x0 x1))) ::' rest , 5)
len-dec-rewrite {- Eta-} ((Id "Eta") :: (InputChar 'η') :: (ParseTree parsed-ws) :: (ParseTree (parsed-evidence x0)) :: (ParseTree parsed-ws) :: _::_(ParseTree (parsed-term x1)) rest) = just (ParseTree (parsed-evidence (norm-evidence (Eta x0 x1))) ::' rest , 6)
len-dec-rewrite {- Evar-} ((Id "Evar") :: _::_(ParseTree (parsed-evar x0)) rest) = just (ParseTree (parsed-levidence (norm-evidence (Evar x0))) ::' rest , 2)
len-dec-rewrite {- Iota-} ((Id "Iota") :: _::_(InputChar 'ι') rest) = just (ParseTree (parsed-ip (norm-ip Iota)) ::' rest , 2)
len-dec-rewrite {- Kcheck-} ((Id "Kcheck") :: (ParseTree (parsed-kind x0)) :: (ParseTree parsed-ows) :: (InputChar '⇐') :: (ParseTree parsed-ows) :: (InputChar '□') :: (ParseTree parsed-ows) :: (InputChar 'b') :: (InputChar 'y') :: (ParseTree parsed-ows) :: (ParseTree (parsed-evidence x1)) :: (ParseTree parsed-ows) :: _::_(InputChar '.') rest) = just (ParseTree (parsed-cmd (norm-cmd (Kcheck x0 x1))) ::' rest , 13)
len-dec-rewrite {- Kdefine-} ((Id "Kdefine") :: (ParseTree (parsed-kvar x0)) :: (ParseTree parsed-ows) :: (InputChar '∷') :: (ParseTree parsed-ows) :: (ParseTree (parsed-kind x1)) :: (ParseTree parsed-ows) :: (InputChar '⇐') :: (ParseTree parsed-ows) :: (InputChar '□') :: (ParseTree parsed-ows) :: (InputChar '=') :: (ParseTree parsed-ows) :: _::_(ParseTree (parsed-evidence x2)) rest) = just (ParseTree (parsed-def (norm-def (Kdefine x0 x1 x2))) ::' rest , 14)
len-dec-rewrite {- Knd-} ((Id "Knd") :: (ParseTree (parsed-type x0)) :: (ParseTree parsed-ows) :: (InputChar '⇐') :: (ParseTree parsed-ows) :: (ParseTree (parsed-kind x1)) :: _::_(Id "Knd_end") rest) = just (ParseTree (parsed-class (norm-class (Knd x0 x1))) ::' rest , 7)
len-dec-rewrite {- KndArrow-} ((ParseTree (parsed-kind x0)) :: (ParseTree parsed-ows) :: (InputChar '→') :: (ParseTree parsed-ows) :: _::_(ParseTree (parsed-kind x1)) rest) = just (ParseTree (parsed-kind (norm-kind (KndArrow x0 x1))) ::' rest , 5)
len-dec-rewrite {- KndParens-} ((Id "KndParens") :: (InputChar '(') :: (ParseTree parsed-ows) :: (ParseTree (parsed-kind x0)) :: (ParseTree parsed-ows) :: _::_(InputChar ')') rest) = just (ParseTree (parsed-kind (norm-kind (KndParens x0))) ::' rest , 6)
len-dec-rewrite {- KndPi-} ((Id "KndPi") :: (InputChar 'Π') :: (ParseTree parsed-ows) :: (ParseTree (parsed-var x0)) :: (ParseTree parsed-ows) :: (InputChar ':') :: (ParseTree parsed-ows) :: (ParseTree (parsed-tk x1)) :: (ParseTree parsed-ows) :: (InputChar '.') :: (ParseTree parsed-ows) :: _::_(ParseTree (parsed-kind x2)) rest) = just (ParseTree (parsed-kind (norm-kind (KndPi x0 x1 x2))) ::' rest , 12)
len-dec-rewrite {- KndTpArrow-} ((Id "KndTpArrow") :: (ParseTree (parsed-ltype x0)) :: (ParseTree parsed-ows) :: (InputChar '→') :: (ParseTree parsed-ows) :: _::_(ParseTree (parsed-kind x1)) rest) = just (ParseTree (parsed-kind (norm-kind (KndTpArrow x0 x1))) ::' rest , 6)
len-dec-rewrite {- KndVar-} ((Id "KndVar") :: _::_(ParseTree (parsed-kvar x0)) rest) = just (ParseTree (parsed-kind (norm-kind (KndVar x0))) ::' rest , 2)
len-dec-rewrite {- Lam-} ((Id "Lam") :: (InputChar 'λ') :: (ParseTree parsed-ows) :: (ParseTree (parsed-var x0)) :: (ParseTree parsed-ows) :: (InputChar '.') :: (ParseTree parsed-ows) :: _::_(ParseTree (parsed-term x1)) rest) = just (ParseTree (parsed-term (norm-term (Lam x0 x1))) ::' rest , 8)
len-dec-rewrite {- Lambda-} ((Id "Lambda") :: _::_(InputChar 'λ') rest) = just (ParseTree (parsed-al (norm-al Lambda)) ::' rest , 2)
len-dec-rewrite {- Lft-} ((Id "Lft") :: (InputChar '↑') :: (ParseTree parsed-ows) :: (ParseTree (parsed-term x0)) :: (ParseTree parsed-ows) :: (InputChar ':') :: (ParseTree parsed-ows) :: _::_(ParseTree (parsed-lliftingType x1)) rest) = just (ParseTree (parsed-ltype (norm-type (Lft x0 x1))) ::' rest , 8)
len-dec-rewrite {- LiftArrow-} ((ParseTree (parsed-liftingType x0)) :: (ParseTree parsed-ows) :: (InputChar '→') :: (ParseTree parsed-ows) :: _::_(ParseTree (parsed-liftingType x1)) rest) = just (ParseTree (parsed-liftingType (norm-liftingType (LiftArrow x0 x1))) ::' rest , 5)
len-dec-rewrite {- LiftParens-} ((Id "LiftParens") :: (InputChar '(') :: (ParseTree parsed-ows) :: (ParseTree (parsed-liftingType x0)) :: (ParseTree parsed-ows) :: _::_(InputChar ')') rest) = just (ParseTree (parsed-lliftingType (norm-liftingType (LiftParens x0))) ::' rest , 6)
len-dec-rewrite {- LiftPi-} ((Id "LiftPi") :: (InputChar 'Π') :: (ParseTree parsed-ows) :: (ParseTree (parsed-var x0)) :: (ParseTree parsed-ows) :: (InputChar ':') :: (ParseTree parsed-ows) :: (ParseTree (parsed-type x1)) :: (ParseTree parsed-ows) :: (InputChar '.') :: (ParseTree parsed-ows) :: _::_(ParseTree (parsed-liftingType x2)) rest) = just (ParseTree (parsed-liftingType (norm-liftingType (LiftPi x0 x1 x2))) ::' rest , 12)
len-dec-rewrite {- LiftStar-} ((Id "LiftStar") :: _::_(InputChar '☆') rest) = just (ParseTree (parsed-liftingType (norm-liftingType LiftStar)) ::' rest , 2)
len-dec-rewrite {- LiftTpArrow-} ((Id "LiftTpArrow") :: (ParseTree (parsed-type x0)) :: (ParseTree parsed-ows) :: (InputChar '→') :: (ParseTree parsed-ows) :: _::_(ParseTree (parsed-liftingType x1)) rest) = just (ParseTree (parsed-liftingType (norm-liftingType (LiftTpArrow x0 x1))) ::' rest , 6)
len-dec-rewrite {- Normalize-} ((Id "Normalize") :: (InputChar 'n') :: (InputChar 'o') :: (InputChar 'r') :: (InputChar 'm') :: (ParseTree parsed-ws) :: (ParseTree (parsed-term x0)) :: (ParseTree parsed-ows) :: _::_(InputChar '.') rest) = just (ParseTree (parsed-cmd (norm-cmd (Normalize x0))) ::' rest , 9)
len-dec-rewrite {- Nu-} ((Id "Nu") :: (InputChar 'ν') :: (ParseTree parsed-ows) :: (ParseTree (parsed-var x0)) :: (ParseTree parsed-ows) :: (InputChar ':') :: (ParseTree parsed-ows) :: (ParseTree (parsed-kind x1)) :: (ParseTree parsed-ows) :: (InputChar '|') :: (ParseTree parsed-ows) :: (ParseTree (parsed-ctorset x2)) :: (ParseTree parsed-ows) :: (InputChar '.') :: (ParseTree parsed-ows) :: _::_(ParseTree (parsed-type x3)) rest) = just (ParseTree (parsed-type (norm-type (Nu x0 x1 x2 x3))) ::' rest , 16)
len-dec-rewrite {- One-} ((Id "One") :: _::_(InputChar '1') rest) = just (ParseTree (parsed-index (norm-index One)) ::' rest , 2)
len-dec-rewrite {- P0-} ((Id "P0") :: _::_(InputChar 'a') rest) = just (ParseTree (parsed-varone-range-1 (string-append 0 (char-to-string 'a'))) ::' rest , 2)
len-dec-rewrite {- P1-} ((Id "P1") :: _::_(InputChar 'b') rest) = just (ParseTree (parsed-varone-range-1 (string-append 0 (char-to-string 'b'))) ::' rest , 2)
len-dec-rewrite {- P10-} ((Id "P10") :: _::_(InputChar 'k') rest) = just (ParseTree (parsed-varone-range-1 (string-append 0 (char-to-string 'k'))) ::' rest , 2)
len-dec-rewrite {- P100-} ((Id "P100") :: _::_(InputChar 'g') rest) = just (ParseTree parsed-anychar-range-9 ::' rest , 2)
len-dec-rewrite {- P101-} ((Id "P101") :: _::_(InputChar 'h') rest) = just (ParseTree parsed-anychar-range-9 ::' rest , 2)
len-dec-rewrite {- P102-} ((Id "P102") :: _::_(InputChar 'i') rest) = just (ParseTree parsed-anychar-range-9 ::' rest , 2)
len-dec-rewrite {- P103-} ((Id "P103") :: _::_(InputChar 'j') rest) = just (ParseTree parsed-anychar-range-9 ::' rest , 2)
len-dec-rewrite {- P104-} ((Id "P104") :: _::_(InputChar 'k') rest) = just (ParseTree parsed-anychar-range-9 ::' rest , 2)
len-dec-rewrite {- P105-} ((Id "P105") :: _::_(InputChar 'l') rest) = just (ParseTree parsed-anychar-range-9 ::' rest , 2)
len-dec-rewrite {- P106-} ((Id "P106") :: _::_(InputChar 'm') rest) = just (ParseTree parsed-anychar-range-9 ::' rest , 2)
len-dec-rewrite {- P107-} ((Id "P107") :: _::_(InputChar 'n') rest) = just (ParseTree parsed-anychar-range-9 ::' rest , 2)
len-dec-rewrite {- P108-} ((Id "P108") :: _::_(InputChar 'o') rest) = just (ParseTree parsed-anychar-range-9 ::' rest , 2)
len-dec-rewrite {- P109-} ((Id "P109") :: _::_(InputChar 'p') rest) = just (ParseTree parsed-anychar-range-9 ::' rest , 2)
len-dec-rewrite {- P11-} ((Id "P11") :: _::_(InputChar 'l') rest) = just (ParseTree (parsed-varone-range-1 (string-append 0 (char-to-string 'l'))) ::' rest , 2)
len-dec-rewrite {- P110-} ((Id "P110") :: _::_(InputChar 'q') rest) = just (ParseTree parsed-anychar-range-9 ::' rest , 2)
len-dec-rewrite {- P111-} ((Id "P111") :: _::_(InputChar 'r') rest) = just (ParseTree parsed-anychar-range-9 ::' rest , 2)
len-dec-rewrite {- P112-} ((Id "P112") :: _::_(InputChar 's') rest) = just (ParseTree parsed-anychar-range-9 ::' rest , 2)
len-dec-rewrite {- P113-} ((Id "P113") :: _::_(InputChar 't') rest) = just (ParseTree parsed-anychar-range-9 ::' rest , 2)
len-dec-rewrite {- P114-} ((Id "P114") :: _::_(InputChar 'u') rest) = just (ParseTree parsed-anychar-range-9 ::' rest , 2)
len-dec-rewrite {- P115-} ((Id "P115") :: _::_(InputChar 'v') rest) = just (ParseTree parsed-anychar-range-9 ::' rest , 2)
len-dec-rewrite {- P116-} ((Id "P116") :: _::_(InputChar 'w') rest) = just (ParseTree parsed-anychar-range-9 ::' rest , 2)
len-dec-rewrite {- P117-} ((Id "P117") :: _::_(InputChar 'x') rest) = just (ParseTree parsed-anychar-range-9 ::' rest , 2)
len-dec-rewrite {- P118-} ((Id "P118") :: _::_(InputChar 'y') rest) = just (ParseTree parsed-anychar-range-9 ::' rest , 2)
len-dec-rewrite {- P119-} ((Id "P119") :: _::_(InputChar 'z') rest) = just (ParseTree parsed-anychar-range-9 ::' rest , 2)
len-dec-rewrite {- P12-} ((Id "P12") :: _::_(InputChar 'm') rest) = just (ParseTree (parsed-varone-range-1 (string-append 0 (char-to-string 'm'))) ::' rest , 2)
len-dec-rewrite {- P120-} ((Id "P120") :: _::_(InputChar '~') rest) = just (ParseTree parsed-anychar-bar-10 ::' rest , 2)
len-dec-rewrite {- P121-} ((Id "P121") :: _::_(InputChar 'η') rest) = just (ParseTree parsed-anychar-bar-10 ::' rest , 2)
len-dec-rewrite {- P122-} ((Id "P122") :: _::_(InputChar '?') rest) = just (ParseTree parsed-anychar-bar-11 ::' rest , 2)
len-dec-rewrite {- P123-} ((Id "P123") :: _::_(ParseTree parsed-anychar-bar-10) rest) = just (ParseTree parsed-anychar-bar-11 ::' rest , 2)
len-dec-rewrite {- P124-} ((Id "P124") :: _::_(InputChar '⇒') rest) = just (ParseTree parsed-anychar-bar-12 ::' rest , 2)
len-dec-rewrite {- P125-} ((Id "P125") :: _::_(ParseTree parsed-anychar-bar-11) rest) = just (ParseTree parsed-anychar-bar-12 ::' rest , 2)
len-dec-rewrite {- P126-} ((Id "P126") :: _::_(InputChar '}') rest) = just (ParseTree parsed-anychar-bar-13 ::' rest , 2)
len-dec-rewrite {- P127-} ((Id "P127") :: _::_(ParseTree parsed-anychar-bar-12) rest) = just (ParseTree parsed-anychar-bar-13 ::' rest , 2)
len-dec-rewrite {- P128-} ((Id "P128") :: _::_(InputChar '{') rest) = just (ParseTree parsed-anychar-bar-14 ::' rest , 2)
len-dec-rewrite {- P129-} ((Id "P129") :: _::_(ParseTree parsed-anychar-bar-13) rest) = just (ParseTree parsed-anychar-bar-14 ::' rest , 2)
len-dec-rewrite {- P13-} ((Id "P13") :: _::_(InputChar 'n') rest) = just (ParseTree (parsed-varone-range-1 (string-append 0 (char-to-string 'n'))) ::' rest , 2)
len-dec-rewrite {- P130-} ((Id "P130") :: _::_(InputChar '-') rest) = just (ParseTree parsed-anychar-bar-15 ::' rest , 2)
len-dec-rewrite {- P131-} ((Id "P131") :: _::_(ParseTree parsed-anychar-bar-14) rest) = just (ParseTree parsed-anychar-bar-15 ::' rest , 2)
len-dec-rewrite {- P132-} ((Id "P132") :: _::_(InputChar '!') rest) = just (ParseTree parsed-anychar-bar-16 ::' rest , 2)
len-dec-rewrite {- P133-} ((Id "P133") :: _::_(ParseTree parsed-anychar-bar-15) rest) = just (ParseTree parsed-anychar-bar-16 ::' rest , 2)
len-dec-rewrite {- P134-} ((Id "P134") :: _::_(InputChar ',') rest) = just (ParseTree parsed-anychar-bar-17 ::' rest , 2)
len-dec-rewrite {- P135-} ((Id "P135") :: _::_(ParseTree parsed-anychar-bar-16) rest) = just (ParseTree parsed-anychar-bar-17 ::' rest , 2)
len-dec-rewrite {- P136-} ((Id "P136") :: _::_(InputChar ']') rest) = just (ParseTree parsed-anychar-bar-18 ::' rest , 2)
len-dec-rewrite {- P137-} ((Id "P137") :: _::_(ParseTree parsed-anychar-bar-17) rest) = just (ParseTree parsed-anychar-bar-18 ::' rest , 2)
len-dec-rewrite {- P138-} ((Id "P138") :: _::_(InputChar '[') rest) = just (ParseTree parsed-anychar-bar-19 ::' rest , 2)
len-dec-rewrite {- P139-} ((Id "P139") :: _::_(ParseTree parsed-anychar-bar-18) rest) = just (ParseTree parsed-anychar-bar-19 ::' rest , 2)
len-dec-rewrite {- P14-} ((Id "P14") :: _::_(InputChar 'o') rest) = just (ParseTree (parsed-varone-range-1 (string-append 0 (char-to-string 'o'))) ::' rest , 2)
len-dec-rewrite {- P140-} ((Id "P140") :: _::_(InputChar 'ζ') rest) = just (ParseTree parsed-anychar-bar-20 ::' rest , 2)
len-dec-rewrite {- P141-} ((Id "P141") :: _::_(ParseTree parsed-anychar-bar-19) rest) = just (ParseTree parsed-anychar-bar-20 ::' rest , 2)
len-dec-rewrite {- P142-} ((Id "P142") :: _::_(InputChar 'δ') rest) = just (ParseTree parsed-anychar-bar-21 ::' rest , 2)
len-dec-rewrite {- P143-} ((Id "P143") :: _::_(ParseTree parsed-anychar-bar-20) rest) = just (ParseTree parsed-anychar-bar-21 ::' rest , 2)
len-dec-rewrite {- P144-} ((Id "P144") :: _::_(InputChar 'β') rest) = just (ParseTree parsed-anychar-bar-22 ::' rest , 2)
len-dec-rewrite {- P145-} ((Id "P145") :: _::_(ParseTree parsed-anychar-bar-21) rest) = just (ParseTree parsed-anychar-bar-22 ::' rest , 2)
len-dec-rewrite {- P146-} ((Id "P146") :: _::_(InputChar 'χ') rest) = just (ParseTree parsed-anychar-bar-23 ::' rest , 2)
len-dec-rewrite {- P147-} ((Id "P147") :: _::_(ParseTree parsed-anychar-bar-22) rest) = just (ParseTree parsed-anychar-bar-23 ::' rest , 2)
len-dec-rewrite {- P148-} ((Id "P148") :: _::_(InputChar '.') rest) = just (ParseTree parsed-anychar-bar-24 ::' rest , 2)
len-dec-rewrite {- P149-} ((Id "P149") :: _::_(ParseTree parsed-anychar-bar-23) rest) = just (ParseTree parsed-anychar-bar-24 ::' rest , 2)
len-dec-rewrite {- P15-} ((Id "P15") :: _::_(InputChar 'p') rest) = just (ParseTree (parsed-varone-range-1 (string-append 0 (char-to-string 'p'))) ::' rest , 2)
len-dec-rewrite {- P150-} ((Id "P150") :: _::_(InputChar ':') rest) = just (ParseTree parsed-anychar-bar-25 ::' rest , 2)
len-dec-rewrite {- P151-} ((Id "P151") :: _::_(ParseTree parsed-anychar-bar-24) rest) = just (ParseTree parsed-anychar-bar-25 ::' rest , 2)
len-dec-rewrite {- P152-} ((Id "P152") :: _::_(InputChar ')') rest) = just (ParseTree parsed-anychar-bar-26 ::' rest , 2)
len-dec-rewrite {- P153-} ((Id "P153") :: _::_(ParseTree parsed-anychar-bar-25) rest) = just (ParseTree parsed-anychar-bar-26 ::' rest , 2)
len-dec-rewrite {- P154-} ((Id "P154") :: _::_(InputChar '(') rest) = just (ParseTree parsed-anychar-bar-27 ::' rest , 2)
len-dec-rewrite {- P155-} ((Id "P155") :: _::_(ParseTree parsed-anychar-bar-26) rest) = just (ParseTree parsed-anychar-bar-27 ::' rest , 2)
len-dec-rewrite {- P156-} ((Id "P156") :: _::_(InputChar '●') rest) = just (ParseTree parsed-anychar-bar-28 ::' rest , 2)
len-dec-rewrite {- P157-} ((Id "P157") :: _::_(ParseTree parsed-anychar-bar-27) rest) = just (ParseTree parsed-anychar-bar-28 ::' rest , 2)
len-dec-rewrite {- P158-} ((Id "P158") :: _::_(InputChar '𝓤') rest) = just (ParseTree parsed-anychar-bar-29 ::' rest , 2)
len-dec-rewrite {- P159-} ((Id "P159") :: _::_(ParseTree parsed-anychar-bar-28) rest) = just (ParseTree parsed-anychar-bar-29 ::' rest , 2)
len-dec-rewrite {- P16-} ((Id "P16") :: _::_(InputChar 'q') rest) = just (ParseTree (parsed-varone-range-1 (string-append 0 (char-to-string 'q'))) ::' rest , 2)
len-dec-rewrite {- P160-} ((Id "P160") :: _::_(InputChar '↑') rest) = just (ParseTree parsed-anychar-bar-30 ::' rest , 2)
len-dec-rewrite {- P161-} ((Id "P161") :: _::_(ParseTree parsed-anychar-bar-29) rest) = just (ParseTree parsed-anychar-bar-30 ::' rest , 2)
len-dec-rewrite {- P162-} ((Id "P162") :: _::_(InputChar '→') rest) = just (ParseTree parsed-anychar-bar-31 ::' rest , 2)
len-dec-rewrite {- P163-} ((Id "P163") :: _::_(ParseTree parsed-anychar-bar-30) rest) = just (ParseTree parsed-anychar-bar-31 ::' rest , 2)
len-dec-rewrite {- P164-} ((Id "P164") :: _::_(InputChar 'ν') rest) = just (ParseTree parsed-anychar-bar-32 ::' rest , 2)
len-dec-rewrite {- P165-} ((Id "P165") :: _::_(ParseTree parsed-anychar-bar-31) rest) = just (ParseTree parsed-anychar-bar-32 ::' rest , 2)
len-dec-rewrite {- P166-} ((Id "P166") :: _::_(InputChar '∈') rest) = just (ParseTree parsed-anychar-bar-33 ::' rest , 2)
len-dec-rewrite {- P167-} ((Id "P167") :: _::_(ParseTree parsed-anychar-bar-32) rest) = just (ParseTree parsed-anychar-bar-33 ::' rest , 2)
len-dec-rewrite {- P168-} ((Id "P168") :: _::_(InputChar '⇐') rest) = just (ParseTree parsed-anychar-bar-34 ::' rest , 2)
len-dec-rewrite {- P169-} ((Id "P169") :: _::_(ParseTree parsed-anychar-bar-33) rest) = just (ParseTree parsed-anychar-bar-34 ::' rest , 2)
len-dec-rewrite {- P17-} ((Id "P17") :: _::_(InputChar 'r') rest) = just (ParseTree (parsed-varone-range-1 (string-append 0 (char-to-string 'r'))) ::' rest , 2)
len-dec-rewrite {- P170-} ((Id "P170") :: _::_(InputChar 'ξ') rest) = just (ParseTree parsed-anychar-bar-35 ::' rest , 2)
len-dec-rewrite {- P171-} ((Id "P171") :: _::_(ParseTree parsed-anychar-bar-34) rest) = just (ParseTree parsed-anychar-bar-35 ::' rest , 2)
len-dec-rewrite {- P172-} ((Id "P172") :: _::_(InputChar '·') rest) = just (ParseTree parsed-anychar-bar-36 ::' rest , 2)
len-dec-rewrite {- P173-} ((Id "P173") :: _::_(ParseTree parsed-anychar-bar-35) rest) = just (ParseTree parsed-anychar-bar-36 ::' rest , 2)
len-dec-rewrite {- P174-} ((Id "P174") :: _::_(InputChar '☆') rest) = just (ParseTree parsed-anychar-bar-37 ::' rest , 2)
len-dec-rewrite {- P175-} ((Id "P175") :: _::_(ParseTree parsed-anychar-bar-36) rest) = just (ParseTree parsed-anychar-bar-37 ::' rest , 2)
len-dec-rewrite {- P176-} ((Id "P176") :: _::_(InputChar '★') rest) = just (ParseTree parsed-anychar-bar-38 ::' rest , 2)
len-dec-rewrite {- P177-} ((Id "P177") :: _::_(ParseTree parsed-anychar-bar-37) rest) = just (ParseTree parsed-anychar-bar-38 ::' rest , 2)
len-dec-rewrite {- P178-} ((Id "P178") :: _::_(InputChar 'π') rest) = just (ParseTree parsed-anychar-bar-39 ::' rest , 2)
len-dec-rewrite {- P179-} ((Id "P179") :: _::_(ParseTree parsed-anychar-bar-38) rest) = just (ParseTree parsed-anychar-bar-39 ::' rest , 2)
len-dec-rewrite {- P18-} ((Id "P18") :: _::_(InputChar 's') rest) = just (ParseTree (parsed-varone-range-1 (string-append 0 (char-to-string 's'))) ::' rest , 2)
len-dec-rewrite {- P180-} ((Id "P180") :: _::_(InputChar '∀') rest) = just (ParseTree parsed-anychar-bar-40 ::' rest , 2)
len-dec-rewrite {- P181-} ((Id "P181") :: _::_(ParseTree parsed-anychar-bar-39) rest) = just (ParseTree parsed-anychar-bar-40 ::' rest , 2)
len-dec-rewrite {- P182-} ((Id "P182") :: _::_(InputChar 'λ') rest) = just (ParseTree parsed-anychar-bar-41 ::' rest , 2)
len-dec-rewrite {- P183-} ((Id "P183") :: _::_(ParseTree parsed-anychar-bar-40) rest) = just (ParseTree parsed-anychar-bar-41 ::' rest , 2)
len-dec-rewrite {- P184-} ((Id "P184") :: _::_(InputChar 'ι') rest) = just (ParseTree parsed-anychar-bar-42 ::' rest , 2)
len-dec-rewrite {- P185-} ((Id "P185") :: _::_(ParseTree parsed-anychar-bar-41) rest) = just (ParseTree parsed-anychar-bar-42 ::' rest , 2)
len-dec-rewrite {- P186-} ((Id "P186") :: _::_(InputChar 'Π') rest) = just (ParseTree parsed-anychar-bar-43 ::' rest , 2)
len-dec-rewrite {- P187-} ((Id "P187") :: _::_(ParseTree parsed-anychar-bar-42) rest) = just (ParseTree parsed-anychar-bar-43 ::' rest , 2)
len-dec-rewrite {- P188-} ((Id "P188") :: _::_(InputChar '□') rest) = just (ParseTree parsed-anychar-bar-44 ::' rest , 2)
len-dec-rewrite {- P189-} ((Id "P189") :: _::_(ParseTree parsed-anychar-bar-43) rest) = just (ParseTree parsed-anychar-bar-44 ::' rest , 2)
len-dec-rewrite {- P19-} ((Id "P19") :: _::_(InputChar 't') rest) = just (ParseTree (parsed-varone-range-1 (string-append 0 (char-to-string 't'))) ::' rest , 2)
len-dec-rewrite {- P190-} ((Id "P190") :: _::_(InputChar '✓') rest) = just (ParseTree parsed-anychar-bar-45 ::' rest , 2)
len-dec-rewrite {- P191-} ((Id "P191") :: _::_(ParseTree parsed-anychar-bar-44) rest) = just (ParseTree parsed-anychar-bar-45 ::' rest , 2)
len-dec-rewrite {- P192-} ((Id "P192") :: _::_(InputChar '∷') rest) = just (ParseTree parsed-anychar-bar-46 ::' rest , 2)
len-dec-rewrite {- P193-} ((Id "P193") :: _::_(ParseTree parsed-anychar-bar-45) rest) = just (ParseTree parsed-anychar-bar-46 ::' rest , 2)
len-dec-rewrite {- P194-} ((Id "P194") :: _::_(InputChar '\'') rest) = just (ParseTree parsed-anychar-bar-47 ::' rest , 2)
len-dec-rewrite {- P195-} ((Id "P195") :: _::_(ParseTree parsed-anychar-bar-46) rest) = just (ParseTree parsed-anychar-bar-47 ::' rest , 2)
len-dec-rewrite {- P196-} ((Id "P196") :: _::_(InputChar '2') rest) = just (ParseTree parsed-anychar-bar-48 ::' rest , 2)
len-dec-rewrite {- P197-} ((Id "P197") :: _::_(ParseTree parsed-anychar-bar-47) rest) = just (ParseTree parsed-anychar-bar-48 ::' rest , 2)
len-dec-rewrite {- P198-} ((Id "P198") :: _::_(InputChar '1') rest) = just (ParseTree parsed-anychar-bar-49 ::' rest , 2)
len-dec-rewrite {- P199-} ((Id "P199") :: _::_(ParseTree parsed-anychar-bar-48) rest) = just (ParseTree parsed-anychar-bar-49 ::' rest , 2)
len-dec-rewrite {- P2-} ((Id "P2") :: _::_(InputChar 'c') rest) = just (ParseTree (parsed-varone-range-1 (string-append 0 (char-to-string 'c'))) ::' rest , 2)
len-dec-rewrite {- P20-} ((Id "P20") :: _::_(InputChar 'u') rest) = just (ParseTree (parsed-varone-range-1 (string-append 0 (char-to-string 'u'))) ::' rest , 2)
len-dec-rewrite {- P200-} ((Id "P200") :: _::_(InputChar '%') rest) = just (ParseTree parsed-anychar-bar-50 ::' rest , 2)
len-dec-rewrite {- P201-} ((Id "P201") :: _::_(ParseTree parsed-anychar-bar-49) rest) = just (ParseTree parsed-anychar-bar-50 ::' rest , 2)
len-dec-rewrite {- P202-} ((Id "P202") :: _::_(InputChar '𝒌') rest) = just (ParseTree parsed-anychar-bar-51 ::' rest , 2)
len-dec-rewrite {- P203-} ((Id "P203") :: _::_(ParseTree parsed-anychar-bar-50) rest) = just (ParseTree parsed-anychar-bar-51 ::' rest , 2)
len-dec-rewrite {- P204-} ((Id "P204") :: _::_(InputChar ' ') rest) = just (ParseTree parsed-anychar-bar-52 ::' rest , 2)
len-dec-rewrite {- P205-} ((Id "P205") :: _::_(ParseTree parsed-anychar-bar-51) rest) = just (ParseTree parsed-anychar-bar-52 ::' rest , 2)
len-dec-rewrite {- P206-} ((Id "P206") :: _::_(InputChar '\t') rest) = just (ParseTree parsed-anychar-bar-53 ::' rest , 2)
len-dec-rewrite {- P207-} ((Id "P207") :: _::_(ParseTree parsed-anychar-bar-52) rest) = just (ParseTree parsed-anychar-bar-53 ::' rest , 2)
len-dec-rewrite {- P208-} ((Id "P208") :: _::_(ParseTree parsed-anychar-range-9) rest) = just (ParseTree parsed-anychar-bar-54 ::' rest , 2)
len-dec-rewrite {- P209-} ((Id "P209") :: _::_(ParseTree parsed-anychar-bar-53) rest) = just (ParseTree parsed-anychar-bar-54 ::' rest , 2)
len-dec-rewrite {- P21-} ((Id "P21") :: _::_(InputChar 'v') rest) = just (ParseTree (parsed-varone-range-1 (string-append 0 (char-to-string 'v'))) ::' rest , 2)
len-dec-rewrite {- P210-} ((Id "P210") :: _::_(ParseTree parsed-anychar-bar-54) rest) = just (ParseTree parsed-anychar ::' rest , 2)
len-dec-rewrite {- P212-} ((Id "P212") :: (ParseTree parsed-anychar) :: _::_(ParseTree parsed-comment-star-55) rest) = just (ParseTree parsed-comment-star-55 ::' rest , 3)
len-dec-rewrite {- P213-} ((Id "P213") :: (InputChar '%') :: (ParseTree parsed-comment-star-55) :: _::_(InputChar '\n') rest) = just (ParseTree parsed-comment ::' rest , 4)
len-dec-rewrite {- P214-} ((Id "P214") :: _::_(InputChar ' ') rest) = just (ParseTree parsed-aws-bar-56 ::' rest , 2)
len-dec-rewrite {- P215-} ((Id "P215") :: _::_(ParseTree parsed-comment) rest) = just (ParseTree parsed-aws-bar-56 ::' rest , 2)
len-dec-rewrite {- P216-} ((Id "P216") :: _::_(InputChar '\t') rest) = just (ParseTree parsed-aws-bar-57 ::' rest , 2)
len-dec-rewrite {- P217-} ((Id "P217") :: _::_(ParseTree parsed-aws-bar-56) rest) = just (ParseTree parsed-aws-bar-57 ::' rest , 2)
len-dec-rewrite {- P218-} ((Id "P218") :: _::_(InputChar '\n') rest) = just (ParseTree parsed-aws-bar-58 ::' rest , 2)
len-dec-rewrite {- P219-} ((Id "P219") :: _::_(ParseTree parsed-aws-bar-57) rest) = just (ParseTree parsed-aws-bar-58 ::' rest , 2)
len-dec-rewrite {- P22-} ((Id "P22") :: _::_(InputChar 'w') rest) = just (ParseTree (parsed-varone-range-1 (string-append 0 (char-to-string 'w'))) ::' rest , 2)
len-dec-rewrite {- P220-} ((Id "P220") :: _::_(ParseTree parsed-aws-bar-58) rest) = just (ParseTree parsed-aws ::' rest , 2)
len-dec-rewrite {- P221-} ((Id "P221") :: _::_(ParseTree parsed-aws) rest) = just (ParseTree parsed-ws-plus-59 ::' rest , 2)
len-dec-rewrite {- P222-} ((Id "P222") :: (ParseTree parsed-aws) :: _::_(ParseTree parsed-ws-plus-59) rest) = just (ParseTree parsed-ws-plus-59 ::' rest , 3)
len-dec-rewrite {- P223-} ((Id "P223") :: _::_(ParseTree parsed-ws-plus-59) rest) = just (ParseTree parsed-ws ::' rest , 2)
len-dec-rewrite {- P225-} ((Id "P225") :: (ParseTree parsed-aws) :: _::_(ParseTree parsed-ows-star-60) rest) = just (ParseTree parsed-ows-star-60 ::' rest , 3)
len-dec-rewrite {- P226-} ((Id "P226") :: _::_(ParseTree parsed-ows-star-60) rest) = just (ParseTree parsed-ows ::' rest , 2)
len-dec-rewrite {- P23-} ((Id "P23") :: _::_(InputChar 'x') rest) = just (ParseTree (parsed-varone-range-1 (string-append 0 (char-to-string 'x'))) ::' rest , 2)
len-dec-rewrite {- P24-} ((Id "P24") :: _::_(InputChar 'y') rest) = just (ParseTree (parsed-varone-range-1 (string-append 0 (char-to-string 'y'))) ::' rest , 2)
len-dec-rewrite {- P25-} ((Id "P25") :: _::_(InputChar 'z') rest) = just (ParseTree (parsed-varone-range-1 (string-append 0 (char-to-string 'z'))) ::' rest , 2)
len-dec-rewrite {- P26-} ((Id "P26") :: _::_(InputChar 'A') rest) = just (ParseTree (parsed-varone-range-2 (string-append 0 (char-to-string 'A'))) ::' rest , 2)
len-dec-rewrite {- P27-} ((Id "P27") :: _::_(InputChar 'B') rest) = just (ParseTree (parsed-varone-range-2 (string-append 0 (char-to-string 'B'))) ::' rest , 2)
len-dec-rewrite {- P28-} ((Id "P28") :: _::_(InputChar 'C') rest) = just (ParseTree (parsed-varone-range-2 (string-append 0 (char-to-string 'C'))) ::' rest , 2)
len-dec-rewrite {- P29-} ((Id "P29") :: _::_(InputChar 'D') rest) = just (ParseTree (parsed-varone-range-2 (string-append 0 (char-to-string 'D'))) ::' rest , 2)
len-dec-rewrite {- P3-} ((Id "P3") :: _::_(InputChar 'd') rest) = just (ParseTree (parsed-varone-range-1 (string-append 0 (char-to-string 'd'))) ::' rest , 2)
len-dec-rewrite {- P30-} ((Id "P30") :: _::_(InputChar 'E') rest) = just (ParseTree (parsed-varone-range-2 (string-append 0 (char-to-string 'E'))) ::' rest , 2)
len-dec-rewrite {- P31-} ((Id "P31") :: _::_(InputChar 'F') rest) = just (ParseTree (parsed-varone-range-2 (string-append 0 (char-to-string 'F'))) ::' rest , 2)
len-dec-rewrite {- P32-} ((Id "P32") :: _::_(InputChar 'G') rest) = just (ParseTree (parsed-varone-range-2 (string-append 0 (char-to-string 'G'))) ::' rest , 2)
len-dec-rewrite {- P33-} ((Id "P33") :: _::_(InputChar 'H') rest) = just (ParseTree (parsed-varone-range-2 (string-append 0 (char-to-string 'H'))) ::' rest , 2)
len-dec-rewrite {- P34-} ((Id "P34") :: _::_(InputChar 'I') rest) = just (ParseTree (parsed-varone-range-2 (string-append 0 (char-to-string 'I'))) ::' rest , 2)
len-dec-rewrite {- P35-} ((Id "P35") :: _::_(InputChar 'J') rest) = just (ParseTree (parsed-varone-range-2 (string-append 0 (char-to-string 'J'))) ::' rest , 2)
len-dec-rewrite {- P36-} ((Id "P36") :: _::_(InputChar 'K') rest) = just (ParseTree (parsed-varone-range-2 (string-append 0 (char-to-string 'K'))) ::' rest , 2)
len-dec-rewrite {- P37-} ((Id "P37") :: _::_(InputChar 'L') rest) = just (ParseTree (parsed-varone-range-2 (string-append 0 (char-to-string 'L'))) ::' rest , 2)
len-dec-rewrite {- P38-} ((Id "P38") :: _::_(InputChar 'M') rest) = just (ParseTree (parsed-varone-range-2 (string-append 0 (char-to-string 'M'))) ::' rest , 2)
len-dec-rewrite {- P39-} ((Id "P39") :: _::_(InputChar 'N') rest) = just (ParseTree (parsed-varone-range-2 (string-append 0 (char-to-string 'N'))) ::' rest , 2)
len-dec-rewrite {- P4-} ((Id "P4") :: _::_(InputChar 'e') rest) = just (ParseTree (parsed-varone-range-1 (string-append 0 (char-to-string 'e'))) ::' rest , 2)
len-dec-rewrite {- P40-} ((Id "P40") :: _::_(InputChar 'O') rest) = just (ParseTree (parsed-varone-range-2 (string-append 0 (char-to-string 'O'))) ::' rest , 2)
len-dec-rewrite {- P41-} ((Id "P41") :: _::_(InputChar 'P') rest) = just (ParseTree (parsed-varone-range-2 (string-append 0 (char-to-string 'P'))) ::' rest , 2)
len-dec-rewrite {- P42-} ((Id "P42") :: _::_(InputChar 'Q') rest) = just (ParseTree (parsed-varone-range-2 (string-append 0 (char-to-string 'Q'))) ::' rest , 2)
len-dec-rewrite {- P43-} ((Id "P43") :: _::_(InputChar 'R') rest) = just (ParseTree (parsed-varone-range-2 (string-append 0 (char-to-string 'R'))) ::' rest , 2)
len-dec-rewrite {- P44-} ((Id "P44") :: _::_(InputChar 'S') rest) = just (ParseTree (parsed-varone-range-2 (string-append 0 (char-to-string 'S'))) ::' rest , 2)
len-dec-rewrite {- P45-} ((Id "P45") :: _::_(InputChar 'T') rest) = just (ParseTree (parsed-varone-range-2 (string-append 0 (char-to-string 'T'))) ::' rest , 2)
len-dec-rewrite {- P46-} ((Id "P46") :: _::_(InputChar 'U') rest) = just (ParseTree (parsed-varone-range-2 (string-append 0 (char-to-string 'U'))) ::' rest , 2)
len-dec-rewrite {- P47-} ((Id "P47") :: _::_(InputChar 'V') rest) = just (ParseTree (parsed-varone-range-2 (string-append 0 (char-to-string 'V'))) ::' rest , 2)
len-dec-rewrite {- P48-} ((Id "P48") :: _::_(InputChar 'W') rest) = just (ParseTree (parsed-varone-range-2 (string-append 0 (char-to-string 'W'))) ::' rest , 2)
len-dec-rewrite {- P49-} ((Id "P49") :: _::_(InputChar 'X') rest) = just (ParseTree (parsed-varone-range-2 (string-append 0 (char-to-string 'X'))) ::' rest , 2)
len-dec-rewrite {- P5-} ((Id "P5") :: _::_(InputChar 'f') rest) = just (ParseTree (parsed-varone-range-1 (string-append 0 (char-to-string 'f'))) ::' rest , 2)
len-dec-rewrite {- P50-} ((Id "P50") :: _::_(InputChar 'Y') rest) = just (ParseTree (parsed-varone-range-2 (string-append 0 (char-to-string 'Y'))) ::' rest , 2)
len-dec-rewrite {- P51-} ((Id "P51") :: _::_(InputChar 'Z') rest) = just (ParseTree (parsed-varone-range-2 (string-append 0 (char-to-string 'Z'))) ::' rest , 2)
len-dec-rewrite {- P52-} ((Id "P52") :: _::_(InputChar '\'') rest) = just (ParseTree (parsed-varone-bar-3 (string-append 0 (char-to-string '\''))) ::' rest , 2)
len-dec-rewrite {- P53-} ((Id "P53") :: _::_(InputChar '-') rest) = just (ParseTree (parsed-varone-bar-3 (string-append 0 (char-to-string '-'))) ::' rest , 2)
len-dec-rewrite {- P54-} ((Id "P54") :: _::_(ParseTree (parsed-varone-range-2 x0)) rest) = just (ParseTree (parsed-varone-bar-4 (string-append 0 x0)) ::' rest , 2)
len-dec-rewrite {- P55-} ((Id "P55") :: _::_(ParseTree (parsed-varone-bar-3 x0)) rest) = just (ParseTree (parsed-varone-bar-4 (string-append 0 x0)) ::' rest , 2)
len-dec-rewrite {- P56-} ((Id "P56") :: _::_(ParseTree (parsed-varone-range-1 x0)) rest) = just (ParseTree (parsed-varone-bar-5 (string-append 0 x0)) ::' rest , 2)
len-dec-rewrite {- P57-} ((Id "P57") :: _::_(ParseTree (parsed-varone-bar-4 x0)) rest) = just (ParseTree (parsed-varone-bar-5 (string-append 0 x0)) ::' rest , 2)
len-dec-rewrite {- P58-} ((Id "P58") :: _::_(ParseTree (parsed-varone-bar-5 x0)) rest) = just (ParseTree (parsed-varone (string-append 0 x0)) ::' rest , 2)
len-dec-rewrite {- P59-} ((Id "P59") :: _::_(ParseTree (parsed-var x0)) rest) = just (ParseTree (parsed-kvar-opt-6 (string-append 0 x0)) ::' rest , 2)
len-dec-rewrite {- P6-} ((Id "P6") :: _::_(InputChar 'g') rest) = just (ParseTree (parsed-varone-range-1 (string-append 0 (char-to-string 'g'))) ::' rest , 2)
len-dec-rewrite {- P61-} ((Id "P61") :: (InputChar '𝒌') :: _::_(ParseTree (parsed-kvar-opt-6 x0)) rest) = just (ParseTree (parsed-kvar (string-append 1 (char-to-string '𝒌') x0)) ::' rest , 3)
len-dec-rewrite {- P62-} ((Id "P62") :: _::_(ParseTree (parsed-varone x0)) rest) = just (ParseTree (parsed-var-plus-7 (string-append 0 x0)) ::' rest , 2)
len-dec-rewrite {- P63-} ((Id "P63") :: (ParseTree (parsed-varone x0)) :: _::_(ParseTree (parsed-var-plus-7 x1)) rest) = just (ParseTree (parsed-var-plus-7 (string-append 1 x0 x1)) ::' rest , 3)
len-dec-rewrite {- P64-} ((Id "P64") :: _::_(ParseTree (parsed-var-plus-7 x0)) rest) = just (ParseTree (parsed-var (string-append 0 x0)) ::' rest , 2)
len-dec-rewrite {- P65-} ((Id "P65") :: _::_(ParseTree (parsed-var x0)) rest) = just (ParseTree (parsed-evar-bar-8 (string-append 0 x0)) ::' rest , 2)
len-dec-rewrite {- P66-} ((Id "P66") :: _::_(ParseTree (parsed-kvar x0)) rest) = just (ParseTree (parsed-evar-bar-8 (string-append 0 x0)) ::' rest , 2)
len-dec-rewrite {- P67-} ((Id "P67") :: _::_(ParseTree (parsed-evar-bar-8 x0)) rest) = just (ParseTree (parsed-evar (string-append 0 x0)) ::' rest , 2)
len-dec-rewrite {- P68-} ((Id "P68") :: _::_(InputChar 'A') rest) = just (ParseTree parsed-anychar-range-9 ::' rest , 2)
len-dec-rewrite {- P69-} ((Id "P69") :: _::_(InputChar 'B') rest) = just (ParseTree parsed-anychar-range-9 ::' rest , 2)
len-dec-rewrite {- P7-} ((Id "P7") :: _::_(InputChar 'h') rest) = just (ParseTree (parsed-varone-range-1 (string-append 0 (char-to-string 'h'))) ::' rest , 2)
len-dec-rewrite {- P70-} ((Id "P70") :: _::_(InputChar 'C') rest) = just (ParseTree parsed-anychar-range-9 ::' rest , 2)
len-dec-rewrite {- P71-} ((Id "P71") :: _::_(InputChar 'D') rest) = just (ParseTree parsed-anychar-range-9 ::' rest , 2)
len-dec-rewrite {- P72-} ((Id "P72") :: _::_(InputChar 'E') rest) = just (ParseTree parsed-anychar-range-9 ::' rest , 2)
len-dec-rewrite {- P73-} ((Id "P73") :: _::_(InputChar 'F') rest) = just (ParseTree parsed-anychar-range-9 ::' rest , 2)
len-dec-rewrite {- P74-} ((Id "P74") :: _::_(InputChar 'G') rest) = just (ParseTree parsed-anychar-range-9 ::' rest , 2)
len-dec-rewrite {- P75-} ((Id "P75") :: _::_(InputChar 'H') rest) = just (ParseTree parsed-anychar-range-9 ::' rest , 2)
len-dec-rewrite {- P76-} ((Id "P76") :: _::_(InputChar 'I') rest) = just (ParseTree parsed-anychar-range-9 ::' rest , 2)
len-dec-rewrite {- P77-} ((Id "P77") :: _::_(InputChar 'J') rest) = just (ParseTree parsed-anychar-range-9 ::' rest , 2)
len-dec-rewrite {- P78-} ((Id "P78") :: _::_(InputChar 'K') rest) = just (ParseTree parsed-anychar-range-9 ::' rest , 2)
len-dec-rewrite {- P79-} ((Id "P79") :: _::_(InputChar 'L') rest) = just (ParseTree parsed-anychar-range-9 ::' rest , 2)
len-dec-rewrite {- P8-} ((Id "P8") :: _::_(InputChar 'i') rest) = just (ParseTree (parsed-varone-range-1 (string-append 0 (char-to-string 'i'))) ::' rest , 2)
len-dec-rewrite {- P80-} ((Id "P80") :: _::_(InputChar 'M') rest) = just (ParseTree parsed-anychar-range-9 ::' rest , 2)
len-dec-rewrite {- P81-} ((Id "P81") :: _::_(InputChar 'N') rest) = just (ParseTree parsed-anychar-range-9 ::' rest , 2)
len-dec-rewrite {- P82-} ((Id "P82") :: _::_(InputChar 'O') rest) = just (ParseTree parsed-anychar-range-9 ::' rest , 2)
len-dec-rewrite {- P83-} ((Id "P83") :: _::_(InputChar 'P') rest) = just (ParseTree parsed-anychar-range-9 ::' rest , 2)
len-dec-rewrite {- P84-} ((Id "P84") :: _::_(InputChar 'Q') rest) = just (ParseTree parsed-anychar-range-9 ::' rest , 2)
len-dec-rewrite {- P85-} ((Id "P85") :: _::_(InputChar 'R') rest) = just (ParseTree parsed-anychar-range-9 ::' rest , 2)
len-dec-rewrite {- P86-} ((Id "P86") :: _::_(InputChar 'S') rest) = just (ParseTree parsed-anychar-range-9 ::' rest , 2)
len-dec-rewrite {- P87-} ((Id "P87") :: _::_(InputChar 'T') rest) = just (ParseTree parsed-anychar-range-9 ::' rest , 2)
len-dec-rewrite {- P88-} ((Id "P88") :: _::_(InputChar 'U') rest) = just (ParseTree parsed-anychar-range-9 ::' rest , 2)
len-dec-rewrite {- P89-} ((Id "P89") :: _::_(InputChar 'V') rest) = just (ParseTree parsed-anychar-range-9 ::' rest , 2)
len-dec-rewrite {- P9-} ((Id "P9") :: _::_(InputChar 'j') rest) = just (ParseTree (parsed-varone-range-1 (string-append 0 (char-to-string 'j'))) ::' rest , 2)
len-dec-rewrite {- P90-} ((Id "P90") :: _::_(InputChar 'W') rest) = just (ParseTree parsed-anychar-range-9 ::' rest , 2)
len-dec-rewrite {- P91-} ((Id "P91") :: _::_(InputChar 'X') rest) = just (ParseTree parsed-anychar-range-9 ::' rest , 2)
len-dec-rewrite {- P92-} ((Id "P92") :: _::_(InputChar 'Y') rest) = just (ParseTree parsed-anychar-range-9 ::' rest , 2)
len-dec-rewrite {- P93-} ((Id "P93") :: _::_(InputChar 'Z') rest) = just (ParseTree parsed-anychar-range-9 ::' rest , 2)
len-dec-rewrite {- P94-} ((Id "P94") :: _::_(InputChar 'a') rest) = just (ParseTree parsed-anychar-range-9 ::' rest , 2)
len-dec-rewrite {- P95-} ((Id "P95") :: _::_(InputChar 'b') rest) = just (ParseTree parsed-anychar-range-9 ::' rest , 2)
len-dec-rewrite {- P96-} ((Id "P96") :: _::_(InputChar 'c') rest) = just (ParseTree parsed-anychar-range-9 ::' rest , 2)
len-dec-rewrite {- P97-} ((Id "P97") :: _::_(InputChar 'd') rest) = just (ParseTree parsed-anychar-range-9 ::' rest , 2)
len-dec-rewrite {- P98-} ((Id "P98") :: _::_(InputChar 'e') rest) = just (ParseTree parsed-anychar-range-9 ::' rest , 2)
len-dec-rewrite {- P99-} ((Id "P99") :: _::_(InputChar 'f') rest) = just (ParseTree parsed-anychar-range-9 ::' rest , 2)
len-dec-rewrite {- Pair-} ((Id "Pair") :: (InputChar '[') :: (ParseTree parsed-ows) :: (ParseTree (parsed-evidence x0)) :: (ParseTree parsed-ows) :: (InputChar ',') :: (ParseTree parsed-ows) :: (ParseTree (parsed-evidence x1)) :: (ParseTree parsed-ows) :: _::_(InputChar ']') rest) = just (ParseTree (parsed-evidence (norm-evidence (Pair x0 x1))) ::' rest , 10)
len-dec-rewrite {- Parens-} ((Id "Parens") :: (InputChar '(') :: (ParseTree parsed-ows) :: (ParseTree (parsed-term x0)) :: (ParseTree parsed-ows) :: _::_(InputChar ')') rest) = just (ParseTree (parsed-lterm (norm-term (Parens x0))) ::' rest , 6)
len-dec-rewrite {- Pi-} ((Id "Pi") :: _::_(InputChar 'Π') rest) = just (ParseTree (parsed-ip (norm-ip Pi)) ::' rest , 2)
len-dec-rewrite {- Print-} ((Id "Print") :: (InputChar 'p') :: (InputChar 'r') :: (InputChar 'i') :: (InputChar 'n') :: (InputChar 't') :: (ParseTree parsed-ws) :: (ParseTree (parsed-var x0)) :: (ParseTree parsed-ows) :: _::_(InputChar '.') rest) = just (ParseTree (parsed-cmd (norm-cmd (Print x0))) ::' rest , 10)
len-dec-rewrite {- Proj-} ((ParseTree (parsed-levidence x0)) :: (ParseTree parsed-ows) :: (InputChar '.') :: (ParseTree parsed-ows) :: _::_(ParseTree (parsed-index x1)) rest) = just (ParseTree (parsed-levidence (norm-evidence (Proj x0 x1))) ::' rest , 5)
len-dec-rewrite {- Rbeta-} ((Id "Rbeta") :: (InputChar 'r') :: (InputChar 'β') :: (ParseTree parsed-ows) :: (ParseTree (parsed-evidence x0)) :: (ParseTree parsed-ws) :: _::_(ParseTree (parsed-term x1)) rest) = just (ParseTree (parsed-evidence (norm-evidence (Rbeta x0 x1))) ::' rest , 7)
len-dec-rewrite {- Star-} ((Id "Star") :: _::_(InputChar '★') rest) = just (ParseTree (parsed-kind (norm-kind Star)) ::' rest , 2)
len-dec-rewrite {- Sym-} ((Id "Sym") :: (InputChar '~') :: (ParseTree parsed-ows) :: _::_(ParseTree (parsed-levidence x0)) rest) = just (ParseTree (parsed-levidence (norm-evidence (Sym x0))) ::' rest , 4)
len-dec-rewrite {- SynthTerm-} ((Id "SynthTerm") :: (ParseTree (parsed-var x0)) :: (ParseTree parsed-ows) :: (InputChar '∷') :: (ParseTree parsed-ws) :: (ParseTree (parsed-term x1)) :: (ParseTree parsed-ows) :: (InputChar '=') :: (ParseTree parsed-ows) :: (ParseTree (parsed-evidence x2)) :: (ParseTree parsed-ows) :: _::_(InputChar '.') rest) = just (ParseTree (parsed-cmd (norm-cmd (SynthTerm x0 x1 x2))) ::' rest , 12)
len-dec-rewrite {- SynthType-} ((Id "SynthType") :: (ParseTree (parsed-var x0)) :: (ParseTree parsed-ows) :: (InputChar '∷') :: (InputChar 't') :: (InputChar 'y') :: (InputChar 'p') :: (InputChar 'e') :: (ParseTree parsed-ows) :: (ParseTree (parsed-type x1)) :: (ParseTree parsed-ows) :: (InputChar '=') :: (ParseTree parsed-ows) :: (ParseTree (parsed-evidence x2)) :: (ParseTree parsed-ows) :: _::_(InputChar '.') rest) = just (ParseTree (parsed-cmd (norm-cmd (SynthType x0 x1 x2))) ::' rest , 16)
len-dec-rewrite {- Tdefine-} ((Id "Tdefine") :: (ParseTree (parsed-var x0)) :: (ParseTree parsed-ows) :: (InputChar '=') :: (ParseTree parsed-ows) :: _::_(ParseTree (parsed-term x1)) rest) = just (ParseTree (parsed-def (norm-def (Tdefine x0 x1))) ::' rest , 6)
len-dec-rewrite {- Tkk-} ((Id "Tkk") :: (ParseTree (parsed-kind x0)) :: _::_(Id "Tkk_end") rest) = just (ParseTree (parsed-tk (norm-tk (Tkk x0))) ::' rest , 3)
len-dec-rewrite {- Tkt-} ((Id "Tkt") :: _::_(ParseTree (parsed-type x0)) rest) = just (ParseTree (parsed-tk (norm-tk (Tkt x0))) ::' rest , 2)
len-dec-rewrite {- Tp-} ((Id "Tp") :: (ParseTree (parsed-term x0)) :: (ParseTree parsed-ows) :: (InputChar '⇐') :: (ParseTree parsed-ows) :: _::_(ParseTree (parsed-type x1)) rest) = just (ParseTree (parsed-class (norm-class (Tp x0 x1))) ::' rest , 6)
len-dec-rewrite {- TpApp-} ((ParseTree (parsed-ltype x0)) :: (ParseTree parsed-ws) :: (InputChar '·') :: (ParseTree parsed-ws) :: _::_(ParseTree (parsed-ltype x1)) rest) = just (ParseTree (parsed-ltype (norm-type (TpApp x0 x1))) ::' rest , 5)
len-dec-rewrite {- TpAppt-} ((ParseTree (parsed-ltype x0)) :: (ParseTree parsed-ws) :: (ParseTree (parsed-lterm x1)) :: _::_(Id "TpAppt_end") rest) = just (ParseTree (parsed-ltype (norm-type (TpAppt x0 x1))) ::' rest , 4)
len-dec-rewrite {- TpArrow-} ((Id "TpArrow") :: (ParseTree (parsed-ltype x0)) :: (ParseTree parsed-ows) :: (InputChar '→') :: (ParseTree parsed-ows) :: _::_(ParseTree (parsed-type x1)) rest) = just (ParseTree (parsed-type (norm-type (TpArrow x0 x1))) ::' rest , 6)
len-dec-rewrite {- TpParens-} ((Id "TpParens") :: (InputChar '(') :: (ParseTree parsed-ows) :: (ParseTree (parsed-type x0)) :: (ParseTree parsed-ows) :: _::_(InputChar ')') rest) = just (ParseTree (parsed-ltype (norm-type (TpParens x0))) ::' rest , 6)
len-dec-rewrite {- TpVar-} ((Id "TpVar") :: _::_(ParseTree (parsed-var x0)) rest) = just (ParseTree (parsed-ltype (norm-type (TpVar x0))) ::' rest , 2)
len-dec-rewrite {- Trans-} ((ParseTree (parsed-levidence x0)) :: (ParseTree parsed-ows) :: (InputChar '·') :: (ParseTree parsed-ows) :: _::_(ParseTree (parsed-levidence x1)) rest) = just (ParseTree (parsed-levidence (norm-evidence (Trans x0 x1))) ::' rest , 5)
len-dec-rewrite {- Two-} ((Id "Two") :: _::_(InputChar '2') rest) = just (ParseTree (parsed-index (norm-index Two)) ::' rest , 2)
len-dec-rewrite {- U-} ((Id "U") :: _::_(InputChar '𝓤') rest) = just (ParseTree (parsed-ltype (norm-type U)) ::' rest , 2)
len-dec-rewrite {- Var-} ((Id "Var") :: _::_(ParseTree (parsed-var x0)) rest) = just (ParseTree (parsed-lterm (norm-term (Var x0))) ::' rest , 2)
len-dec-rewrite {- Xi-} ((Id "Xi") :: (InputChar 'ξ') :: (ParseTree parsed-ows) :: (ParseTree (parsed-var x0)) :: (ParseTree (parsed-opt_eclass x1)) :: (ParseTree parsed-ows) :: (InputChar '.') :: (ParseTree parsed-ows) :: _::_(ParseTree (parsed-evidence x2)) rest) = just (ParseTree (parsed-evidence (norm-evidence (Xi x0 x1 x2))) ::' rest , 9)
len-dec-rewrite {- checkCast-} ((Id "checkCast") :: _::_(InputChar '⇐') rest) = just (ParseTree (parsed-castDir (norm-castDir checkCast)) ::' rest , 2)
len-dec-rewrite {- embed-} ((Id "embed") :: (ParseTree (parsed-lterm x0)) :: _::_(Id "embed_end") rest) = just (ParseTree (parsed-term x0) ::' rest , 3)
len-dec-rewrite {- embed-} ((Id "embed") :: (ParseTree (parsed-ltype x0)) :: _::_(Id "embed_end") rest) = just (ParseTree (parsed-type x0) ::' rest , 3)
len-dec-rewrite {- embed-} ((Id "embed") :: _::_(ParseTree (parsed-lliftingType x0)) rest) = just (ParseTree (parsed-liftingType x0) ::' rest , 2)
len-dec-rewrite {- embed-} ((Id "embed") :: (ParseTree (parsed-levidence x0)) :: _::_(Id "embed_end") rest) = just (ParseTree (parsed-evidence x0) ::' rest , 3)
len-dec-rewrite {- showCtxtYes-} ((Id "showCtxtYes") :: _::_(InputChar '!') rest) = just (ParseTree (parsed-showCtxt (norm-showCtxt showCtxtYes)) ::' rest , 2)
len-dec-rewrite {- synthCast-} ((Id "synthCast") :: _::_(InputChar '⇒') rest) = just (ParseTree (parsed-castDir (norm-castDir synthCast)) ::' rest , 2)
len-dec-rewrite {- EclassNone-} (_::_(Id "EclassNone") rest) = just (ParseTree (parsed-opt_eclass (norm-opt_eclass EclassNone)) ::' rest , 1)
len-dec-rewrite {- P211-} (_::_(Id "P211") rest) = just (ParseTree parsed-comment-star-55 ::' rest , 1)
len-dec-rewrite {- P224-} (_::_(Id "P224") rest) = just (ParseTree parsed-ows-star-60 ::' rest , 1)
len-dec-rewrite {- P60-} (_::_(Id "P60") rest) = just (ParseTree (parsed-kvar-opt-6 empty-string) ::' rest , 1)
len-dec-rewrite {- showCtxtNo-} (_::_(Id "showCtxtNo") rest) = just (ParseTree (parsed-showCtxt (norm-showCtxt showCtxtNo)) ::' rest , 1)
len-dec-rewrite x = nothing

rrs : rewriteRules
rrs = record { len-dec-rewrite = len-dec-rewrite }
