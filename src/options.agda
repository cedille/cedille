module options where

open import lib

open import options-types public
----------------------------------------------------------------------------------
-- Run-rewriting rules
----------------------------------------------------------------------------------

data gratr2-nt : Set where
  _ws-plus-34 : gratr2-nt
  _ws : gratr2-nt
  _str-bool : gratr2-nt
  _start : gratr2-nt
  _squote : gratr2-nt
  _posinfo : gratr2-nt
  _paths : gratr2-nt
  _path-star-1 : gratr2-nt
  _path : gratr2-nt
  _ows-star-35 : gratr2-nt
  _ows : gratr2-nt
  _opts : gratr2-nt
  _opt : gratr2-nt
  _numpunct-bar-8 : gratr2-nt
  _numpunct-bar-7 : gratr2-nt
  _numpunct : gratr2-nt
  _numone-range-5 : gratr2-nt
  _numone : gratr2-nt
  _num-plus-6 : gratr2-nt
  _num : gratr2-nt
  _comment-star-30 : gratr2-nt
  _comment : gratr2-nt
  _aws-bar-33 : gratr2-nt
  _aws-bar-32 : gratr2-nt
  _aws-bar-31 : gratr2-nt
  _aws : gratr2-nt
  _anychar-bar-9 : gratr2-nt
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
  _alpha-range-3 : gratr2-nt
  _alpha-range-2 : gratr2-nt
  _alpha-bar-4 : gratr2-nt
  _alpha : gratr2-nt


gratr2-nt-eq : gratr2-nt → gratr2-nt → 𝔹
gratr2-nt-eq  _ws-plus-34 _ws-plus-34 = tt
gratr2-nt-eq  _ws _ws = tt
gratr2-nt-eq  _str-bool _str-bool = tt
gratr2-nt-eq  _start _start = tt
gratr2-nt-eq  _squote _squote = tt
gratr2-nt-eq  _posinfo _posinfo = tt
gratr2-nt-eq  _paths _paths = tt
gratr2-nt-eq  _path-star-1 _path-star-1 = tt
gratr2-nt-eq  _path _path = tt
gratr2-nt-eq  _ows-star-35 _ows-star-35 = tt
gratr2-nt-eq  _ows _ows = tt
gratr2-nt-eq  _opts _opts = tt
gratr2-nt-eq  _opt _opt = tt
gratr2-nt-eq  _numpunct-bar-8 _numpunct-bar-8 = tt
gratr2-nt-eq  _numpunct-bar-7 _numpunct-bar-7 = tt
gratr2-nt-eq  _numpunct _numpunct = tt
gratr2-nt-eq  _numone-range-5 _numone-range-5 = tt
gratr2-nt-eq  _numone _numone = tt
gratr2-nt-eq  _num-plus-6 _num-plus-6 = tt
gratr2-nt-eq  _num _num = tt
gratr2-nt-eq  _comment-star-30 _comment-star-30 = tt
gratr2-nt-eq  _comment _comment = tt
gratr2-nt-eq  _aws-bar-33 _aws-bar-33 = tt
gratr2-nt-eq  _aws-bar-32 _aws-bar-32 = tt
gratr2-nt-eq  _aws-bar-31 _aws-bar-31 = tt
gratr2-nt-eq  _aws _aws = tt
gratr2-nt-eq  _anychar-bar-9 _anychar-bar-9 = tt
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
gratr2-nt-eq  _alpha-range-3 _alpha-range-3 = tt
gratr2-nt-eq  _alpha-range-2 _alpha-range-2 = tt
gratr2-nt-eq  _alpha-bar-4 _alpha-bar-4 = tt
gratr2-nt-eq  _alpha _alpha = tt
gratr2-nt-eq _ _ = ff


open import rtn gratr2-nt


options-start : gratr2-nt → 𝕃 gratr2-rule
options-start _ws-plus-34 = (just "P132" , nothing , just _ws-plus-34 , inj₁ _aws :: inj₁ _ws-plus-34 :: []) :: (just "P131" , nothing , just _ws-plus-34 , inj₁ _aws :: []) :: []
options-start _ws = (just "P133" , nothing , just _ws , inj₁ _ws-plus-34 :: []) :: []
options-start _str-bool = (just "StrBoolTrue" , nothing , just _str-bool , inj₂ 't' :: inj₂ 'r' :: inj₂ 'u' :: inj₂ 'e' :: []) :: (just "StrBoolFalse" , nothing , just _str-bool , inj₂ 'f' :: inj₂ 'a' :: inj₂ 'l' :: inj₂ 's' :: inj₂ 'e' :: []) :: []
options-start _start = (just "File" , nothing , just _start , inj₁ _opts :: inj₁ _ows :: []) :: []
options-start _squote = (just "P0" , nothing , just _squote , inj₂ '\"' :: []) :: []
options-start _posinfo = (just "Posinfo" , nothing , just _posinfo , []) :: []
options-start _paths = (just "PathsNil" , nothing , just _paths , []) :: (just "PathsCons" , nothing , just _paths , inj₁ _ws :: inj₁ _path :: inj₁ _paths :: []) :: []
options-start _path-star-1 = (just "P2" , nothing , just _path-star-1 , inj₁ _anychar :: inj₁ _path-star-1 :: []) :: (just "P1" , nothing , just _path-star-1 , []) :: []
options-start _path = (just "P3" , nothing , just _path , inj₁ _squote :: inj₁ _path-star-1 :: inj₁ _squote :: []) :: []
options-start _ows-star-35 = (just "P135" , nothing , just _ows-star-35 , inj₁ _aws :: inj₁ _ows-star-35 :: []) :: (just "P134" , nothing , just _ows-star-35 , []) :: []
options-start _ows = (just "P136" , nothing , just _ows , inj₁ _ows-star-35 :: []) :: []
options-start _opts = (just "OptsNil" , nothing , just _opts , []) :: (just "OptsCons" , nothing , just _opts , inj₁ _ows :: inj₁ _opt :: inj₁ _opts :: []) :: []
options-start _opt = (just "UseCedeFiles" , nothing , just _opt , inj₂ 'u' :: inj₂ 's' :: inj₂ 'e' :: inj₂ '-' :: inj₂ 'c' :: inj₂ 'e' :: inj₂ 'd' :: inj₂ 'e' :: inj₂ '-' :: inj₂ 'f' :: inj₂ 'i' :: inj₂ 'l' :: inj₂ 'e' :: inj₂ 's' :: inj₁ _ows :: inj₂ '=' :: inj₁ _ows :: inj₁ _str-bool :: inj₁ _ows :: inj₂ '.' :: inj₁ _ows :: []) :: (just "ShowQualifiedVars" , nothing , just _opt , inj₂ 's' :: inj₂ 'h' :: inj₂ 'o' :: inj₂ 'w' :: inj₂ '-' :: inj₂ 'q' :: inj₂ 'u' :: inj₂ 'a' :: inj₂ 'l' :: inj₂ 'i' :: inj₂ 'f' :: inj₂ 'i' :: inj₂ 'e' :: inj₂ 'd' :: inj₂ '-' :: inj₂ 'v' :: inj₂ 'a' :: inj₂ 'r' :: inj₂ 's' :: inj₁ _ows :: inj₂ '=' :: inj₁ _ows :: inj₁ _str-bool :: inj₁ _ows :: inj₂ '.' :: inj₁ _ows :: []) :: (just "MakeRktFiles" , nothing , just _opt , inj₂ 'm' :: inj₂ 'a' :: inj₂ 'k' :: inj₂ 'e' :: inj₂ '-' :: inj₂ 'r' :: inj₂ 'k' :: inj₂ 't' :: inj₂ '-' :: inj₂ 'f' :: inj₂ 'i' :: inj₂ 'l' :: inj₂ 'e' :: inj₂ 's' :: inj₁ _ows :: inj₂ '=' :: inj₁ _ows :: inj₁ _str-bool :: inj₁ _ows :: inj₂ '.' :: inj₁ _ows :: []) :: (just "Lib" , nothing , just _opt , inj₂ 'i' :: inj₂ 'm' :: inj₂ 'p' :: inj₂ 'o' :: inj₂ 'r' :: inj₂ 't' :: inj₂ '-' :: inj₂ 'd' :: inj₂ 'i' :: inj₂ 'r' :: inj₂ 'e' :: inj₂ 'c' :: inj₂ 't' :: inj₂ 'o' :: inj₂ 'r' :: inj₂ 'i' :: inj₂ 'e' :: inj₂ 's' :: inj₁ _ows :: inj₂ '=' :: inj₁ _ows :: inj₁ _paths :: inj₁ _ows :: inj₂ '.' :: []) :: (just "GenerateLogs" , nothing , just _opt , inj₂ 'g' :: inj₂ 'e' :: inj₂ 'n' :: inj₂ 'e' :: inj₂ 'r' :: inj₂ 'a' :: inj₂ 't' :: inj₂ 'e' :: inj₂ '-' :: inj₂ 'l' :: inj₂ 'o' :: inj₂ 'g' :: inj₂ 's' :: inj₁ _ows :: inj₂ '=' :: inj₁ _ows :: inj₁ _str-bool :: inj₁ _ows :: inj₂ '.' :: inj₁ _ows :: []) :: []
options-start _numpunct-bar-8 = (just "P76" , nothing , just _numpunct-bar-8 , inj₁ _numpunct-bar-7 :: []) :: (just "P75" , nothing , just _numpunct-bar-8 , inj₁ _numone :: []) :: []
options-start _numpunct-bar-7 = (just "P74" , nothing , just _numpunct-bar-7 , inj₂ '-' :: []) :: (just "P73" , nothing , just _numpunct-bar-7 , inj₂ '\'' :: []) :: []
options-start _numpunct = (just "P77" , nothing , just _numpunct , inj₁ _numpunct-bar-8 :: []) :: []
options-start _numone-range-5 = (just "P68" , nothing , just _numone-range-5 , inj₂ '9' :: []) :: (just "P67" , nothing , just _numone-range-5 , inj₂ '8' :: []) :: (just "P66" , nothing , just _numone-range-5 , inj₂ '7' :: []) :: (just "P65" , nothing , just _numone-range-5 , inj₂ '6' :: []) :: (just "P64" , nothing , just _numone-range-5 , inj₂ '5' :: []) :: (just "P63" , nothing , just _numone-range-5 , inj₂ '4' :: []) :: (just "P62" , nothing , just _numone-range-5 , inj₂ '3' :: []) :: (just "P61" , nothing , just _numone-range-5 , inj₂ '2' :: []) :: (just "P60" , nothing , just _numone-range-5 , inj₂ '1' :: []) :: (just "P59" , nothing , just _numone-range-5 , inj₂ '0' :: []) :: []
options-start _numone = (just "P69" , nothing , just _numone , inj₁ _numone-range-5 :: []) :: []
options-start _num-plus-6 = (just "P71" , nothing , just _num-plus-6 , inj₁ _numone :: inj₁ _num-plus-6 :: []) :: (just "P70" , nothing , just _num-plus-6 , inj₁ _numone :: []) :: []
options-start _num = (just "P72" , nothing , just _num , inj₁ _num-plus-6 :: []) :: []
options-start _comment-star-30 = (just "P122" , nothing , just _comment-star-30 , inj₁ _anychar :: inj₁ _comment-star-30 :: []) :: (just "P121" , nothing , just _comment-star-30 , []) :: []
options-start _comment = (just "P123" , nothing , just _comment , inj₂ '%' :: inj₁ _comment-star-30 :: inj₂ '\n' :: []) :: []
options-start _aws-bar-33 = (just "P129" , nothing , just _aws-bar-33 , inj₁ _aws-bar-32 :: []) :: (just "P128" , nothing , just _aws-bar-33 , inj₂ '\n' :: []) :: []
options-start _aws-bar-32 = (just "P127" , nothing , just _aws-bar-32 , inj₁ _aws-bar-31 :: []) :: (just "P126" , nothing , just _aws-bar-32 , inj₂ '\t' :: []) :: []
options-start _aws-bar-31 = (just "P125" , nothing , just _aws-bar-31 , inj₁ _comment :: []) :: (just "P124" , nothing , just _aws-bar-31 , inj₂ ' ' :: []) :: []
options-start _aws = (just "P130" , nothing , just _aws , inj₁ _aws-bar-33 :: []) :: []
options-start _anychar-bar-9 = (just "P79" , nothing , just _anychar-bar-9 , inj₂ '_' :: []) :: (just "P78" , nothing , just _anychar-bar-9 , inj₂ '/' :: []) :: []
options-start _anychar-bar-29 = (just "P119" , nothing , just _anychar-bar-29 , inj₁ _anychar-bar-28 :: []) :: (just "P118" , nothing , just _anychar-bar-29 , inj₁ _alpha :: []) :: []
options-start _anychar-bar-28 = (just "P117" , nothing , just _anychar-bar-28 , inj₁ _anychar-bar-27 :: []) :: (just "P116" , nothing , just _anychar-bar-28 , inj₁ _numpunct :: []) :: []
options-start _anychar-bar-27 = (just "P115" , nothing , just _anychar-bar-27 , inj₁ _anychar-bar-26 :: []) :: (just "P114" , nothing , just _anychar-bar-27 , inj₂ '\t' :: []) :: []
options-start _anychar-bar-26 = (just "P113" , nothing , just _anychar-bar-26 , inj₁ _anychar-bar-25 :: []) :: (just "P112" , nothing , just _anychar-bar-26 , inj₂ ' ' :: []) :: []
options-start _anychar-bar-25 = (just "P111" , nothing , just _anychar-bar-25 , inj₁ _anychar-bar-24 :: []) :: (just "P110" , nothing , just _anychar-bar-25 , inj₂ '%' :: []) :: []
options-start _anychar-bar-24 = (just "P109" , nothing , just _anychar-bar-24 , inj₁ _anychar-bar-23 :: []) :: (just "P108" , nothing , just _anychar-bar-24 , inj₂ '(' :: []) :: []
options-start _anychar-bar-23 = (just "P107" , nothing , just _anychar-bar-23 , inj₁ _anychar-bar-22 :: []) :: (just "P106" , nothing , just _anychar-bar-23 , inj₂ ')' :: []) :: []
options-start _anychar-bar-22 = (just "P105" , nothing , just _anychar-bar-22 , inj₁ _anychar-bar-21 :: []) :: (just "P104" , nothing , just _anychar-bar-22 , inj₂ ':' :: []) :: []
options-start _anychar-bar-21 = (just "P103" , nothing , just _anychar-bar-21 , inj₁ _anychar-bar-20 :: []) :: (just "P102" , nothing , just _anychar-bar-21 , inj₂ '.' :: []) :: []
options-start _anychar-bar-20 = (just "P101" , nothing , just _anychar-bar-20 , inj₁ _anychar-bar-19 :: []) :: (just "P100" , nothing , just _anychar-bar-20 , inj₂ '[' :: []) :: []
options-start _anychar-bar-19 = (just "P99" , nothing , just _anychar-bar-19 , inj₁ _anychar-bar-18 :: []) :: (just "P98" , nothing , just _anychar-bar-19 , inj₂ ']' :: []) :: []
options-start _anychar-bar-18 = (just "P97" , nothing , just _anychar-bar-18 , inj₁ _anychar-bar-17 :: []) :: (just "P96" , nothing , just _anychar-bar-18 , inj₂ ',' :: []) :: []
options-start _anychar-bar-17 = (just "P95" , nothing , just _anychar-bar-17 , inj₁ _anychar-bar-16 :: []) :: (just "P94" , nothing , just _anychar-bar-17 , inj₂ '!' :: []) :: []
options-start _anychar-bar-16 = (just "P93" , nothing , just _anychar-bar-16 , inj₁ _anychar-bar-15 :: []) :: (just "P92" , nothing , just _anychar-bar-16 , inj₂ '{' :: []) :: []
options-start _anychar-bar-15 = (just "P91" , nothing , just _anychar-bar-15 , inj₁ _anychar-bar-14 :: []) :: (just "P90" , nothing , just _anychar-bar-15 , inj₂ '}' :: []) :: []
options-start _anychar-bar-14 = (just "P89" , nothing , just _anychar-bar-14 , inj₁ _anychar-bar-13 :: []) :: (just "P88" , nothing , just _anychar-bar-14 , inj₂ '-' :: []) :: []
options-start _anychar-bar-13 = (just "P87" , nothing , just _anychar-bar-13 , inj₁ _anychar-bar-12 :: []) :: (just "P86" , nothing , just _anychar-bar-13 , inj₂ '=' :: []) :: []
options-start _anychar-bar-12 = (just "P85" , nothing , just _anychar-bar-12 , inj₁ _anychar-bar-11 :: []) :: (just "P84" , nothing , just _anychar-bar-12 , inj₂ '+' :: []) :: []
options-start _anychar-bar-11 = (just "P83" , nothing , just _anychar-bar-11 , inj₁ _anychar-bar-10 :: []) :: (just "P82" , nothing , just _anychar-bar-11 , inj₂ '<' :: []) :: []
options-start _anychar-bar-10 = (just "P81" , nothing , just _anychar-bar-10 , inj₁ _anychar-bar-9 :: []) :: (just "P80" , nothing , just _anychar-bar-10 , inj₂ '>' :: []) :: []
options-start _anychar = (just "P120" , nothing , just _anychar , inj₁ _anychar-bar-29 :: []) :: []
options-start _alpha-range-3 = (just "P55" , nothing , just _alpha-range-3 , inj₂ 'Z' :: []) :: (just "P54" , nothing , just _alpha-range-3 , inj₂ 'Y' :: []) :: (just "P53" , nothing , just _alpha-range-3 , inj₂ 'X' :: []) :: (just "P52" , nothing , just _alpha-range-3 , inj₂ 'W' :: []) :: (just "P51" , nothing , just _alpha-range-3 , inj₂ 'V' :: []) :: (just "P50" , nothing , just _alpha-range-3 , inj₂ 'U' :: []) :: (just "P49" , nothing , just _alpha-range-3 , inj₂ 'T' :: []) :: (just "P48" , nothing , just _alpha-range-3 , inj₂ 'S' :: []) :: (just "P47" , nothing , just _alpha-range-3 , inj₂ 'R' :: []) :: (just "P46" , nothing , just _alpha-range-3 , inj₂ 'Q' :: []) :: (just "P45" , nothing , just _alpha-range-3 , inj₂ 'P' :: []) :: (just "P44" , nothing , just _alpha-range-3 , inj₂ 'O' :: []) :: (just "P43" , nothing , just _alpha-range-3 , inj₂ 'N' :: []) :: (just "P42" , nothing , just _alpha-range-3 , inj₂ 'M' :: []) :: (just "P41" , nothing , just _alpha-range-3 , inj₂ 'L' :: []) :: (just "P40" , nothing , just _alpha-range-3 , inj₂ 'K' :: []) :: (just "P39" , nothing , just _alpha-range-3 , inj₂ 'J' :: []) :: (just "P38" , nothing , just _alpha-range-3 , inj₂ 'I' :: []) :: (just "P37" , nothing , just _alpha-range-3 , inj₂ 'H' :: []) :: (just "P36" , nothing , just _alpha-range-3 , inj₂ 'G' :: []) :: (just "P35" , nothing , just _alpha-range-3 , inj₂ 'F' :: []) :: (just "P34" , nothing , just _alpha-range-3 , inj₂ 'E' :: []) :: (just "P33" , nothing , just _alpha-range-3 , inj₂ 'D' :: []) :: (just "P32" , nothing , just _alpha-range-3 , inj₂ 'C' :: []) :: (just "P31" , nothing , just _alpha-range-3 , inj₂ 'B' :: []) :: (just "P30" , nothing , just _alpha-range-3 , inj₂ 'A' :: []) :: []
options-start _alpha-range-2 = (just "P9" , nothing , just _alpha-range-2 , inj₂ 'f' :: []) :: (just "P8" , nothing , just _alpha-range-2 , inj₂ 'e' :: []) :: (just "P7" , nothing , just _alpha-range-2 , inj₂ 'd' :: []) :: (just "P6" , nothing , just _alpha-range-2 , inj₂ 'c' :: []) :: (just "P5" , nothing , just _alpha-range-2 , inj₂ 'b' :: []) :: (just "P4" , nothing , just _alpha-range-2 , inj₂ 'a' :: []) :: (just "P29" , nothing , just _alpha-range-2 , inj₂ 'z' :: []) :: (just "P28" , nothing , just _alpha-range-2 , inj₂ 'y' :: []) :: (just "P27" , nothing , just _alpha-range-2 , inj₂ 'x' :: []) :: (just "P26" , nothing , just _alpha-range-2 , inj₂ 'w' :: []) :: (just "P25" , nothing , just _alpha-range-2 , inj₂ 'v' :: []) :: (just "P24" , nothing , just _alpha-range-2 , inj₂ 'u' :: []) :: (just "P23" , nothing , just _alpha-range-2 , inj₂ 't' :: []) :: (just "P22" , nothing , just _alpha-range-2 , inj₂ 's' :: []) :: (just "P21" , nothing , just _alpha-range-2 , inj₂ 'r' :: []) :: (just "P20" , nothing , just _alpha-range-2 , inj₂ 'q' :: []) :: (just "P19" , nothing , just _alpha-range-2 , inj₂ 'p' :: []) :: (just "P18" , nothing , just _alpha-range-2 , inj₂ 'o' :: []) :: (just "P17" , nothing , just _alpha-range-2 , inj₂ 'n' :: []) :: (just "P16" , nothing , just _alpha-range-2 , inj₂ 'm' :: []) :: (just "P15" , nothing , just _alpha-range-2 , inj₂ 'l' :: []) :: (just "P14" , nothing , just _alpha-range-2 , inj₂ 'k' :: []) :: (just "P13" , nothing , just _alpha-range-2 , inj₂ 'j' :: []) :: (just "P12" , nothing , just _alpha-range-2 , inj₂ 'i' :: []) :: (just "P11" , nothing , just _alpha-range-2 , inj₂ 'h' :: []) :: (just "P10" , nothing , just _alpha-range-2 , inj₂ 'g' :: []) :: []
options-start _alpha-bar-4 = (just "P57" , nothing , just _alpha-bar-4 , inj₁ _alpha-range-3 :: []) :: (just "P56" , nothing , just _alpha-bar-4 , inj₁ _alpha-range-2 :: []) :: []
options-start _alpha = (just "P58" , nothing , just _alpha , inj₁ _alpha-bar-4 :: []) :: []


options-return : maybe gratr2-nt → 𝕃 gratr2-rule
options-return _ = []

options-rtn : gratr2-rtn
options-rtn = record { start = _start ; _eq_ = gratr2-nt-eq ; gratr2-start = options-start ; gratr2-return = options-return }

open import run ptr
open noderiv

------------------------------------------
-- Length-decreasing rules
------------------------------------------

len-dec-rewrite : Run → maybe (Run × ℕ)
len-dec-rewrite {- File-} ((Id "File") :: (ParseTree (parsed-opts x0)) :: _::_(ParseTree parsed-ows) rest) = just (ParseTree (parsed-start (norm-start (File x0))) ::' rest , 3)
len-dec-rewrite {- GenerateLogs-} ((Id "GenerateLogs") :: (InputChar 'g') :: (InputChar 'e') :: (InputChar 'n') :: (InputChar 'e') :: (InputChar 'r') :: (InputChar 'a') :: (InputChar 't') :: (InputChar 'e') :: (InputChar '-') :: (InputChar 'l') :: (InputChar 'o') :: (InputChar 'g') :: (InputChar 's') :: (ParseTree parsed-ows) :: (InputChar '=') :: (ParseTree parsed-ows) :: (ParseTree (parsed-str-bool x0)) :: (ParseTree parsed-ows) :: (InputChar '.') :: _::_(ParseTree parsed-ows) rest) = just (ParseTree (parsed-opt (norm-opt (GenerateLogs x0))) ::' rest , 21)
len-dec-rewrite {- Lib-} ((Id "Lib") :: (InputChar 'i') :: (InputChar 'm') :: (InputChar 'p') :: (InputChar 'o') :: (InputChar 'r') :: (InputChar 't') :: (InputChar '-') :: (InputChar 'd') :: (InputChar 'i') :: (InputChar 'r') :: (InputChar 'e') :: (InputChar 'c') :: (InputChar 't') :: (InputChar 'o') :: (InputChar 'r') :: (InputChar 'i') :: (InputChar 'e') :: (InputChar 's') :: (ParseTree parsed-ows) :: (InputChar '=') :: (ParseTree parsed-ows) :: (ParseTree (parsed-paths x0)) :: (ParseTree parsed-ows) :: _::_(InputChar '.') rest) = just (ParseTree (parsed-opt (norm-opt (Lib x0))) ::' rest , 25)
len-dec-rewrite {- MakeRktFiles-} ((Id "MakeRktFiles") :: (InputChar 'm') :: (InputChar 'a') :: (InputChar 'k') :: (InputChar 'e') :: (InputChar '-') :: (InputChar 'r') :: (InputChar 'k') :: (InputChar 't') :: (InputChar '-') :: (InputChar 'f') :: (InputChar 'i') :: (InputChar 'l') :: (InputChar 'e') :: (InputChar 's') :: (ParseTree parsed-ows) :: (InputChar '=') :: (ParseTree parsed-ows) :: (ParseTree (parsed-str-bool x0)) :: (ParseTree parsed-ows) :: (InputChar '.') :: _::_(ParseTree parsed-ows) rest) = just (ParseTree (parsed-opt (norm-opt (MakeRktFiles x0))) ::' rest , 22)
len-dec-rewrite {- OptsCons-} ((Id "OptsCons") :: (ParseTree parsed-ows) :: (ParseTree (parsed-opt x0)) :: _::_(ParseTree (parsed-opts x1)) rest) = just (ParseTree (parsed-opts (norm-opts (OptsCons x0 x1))) ::' rest , 4)
len-dec-rewrite {- P0-} ((Id "P0") :: _::_(InputChar '\"') rest) = just (ParseTree parsed-squote ::' rest , 2)
len-dec-rewrite {- P10-} ((Id "P10") :: _::_(InputChar 'g') rest) = just (ParseTree (parsed-alpha-range-2 (string-append 0 (char-to-string 'g'))) ::' rest , 2)
len-dec-rewrite {- P100-} ((Id "P100") :: _::_(InputChar '[') rest) = just (ParseTree (parsed-anychar-bar-20 (string-append 0 (char-to-string '['))) ::' rest , 2)
len-dec-rewrite {- P101-} ((Id "P101") :: _::_(ParseTree (parsed-anychar-bar-19 x0)) rest) = just (ParseTree (parsed-anychar-bar-20 (string-append 0 x0)) ::' rest , 2)
len-dec-rewrite {- P102-} ((Id "P102") :: _::_(InputChar '.') rest) = just (ParseTree (parsed-anychar-bar-21 (string-append 0 (char-to-string '.'))) ::' rest , 2)
len-dec-rewrite {- P103-} ((Id "P103") :: _::_(ParseTree (parsed-anychar-bar-20 x0)) rest) = just (ParseTree (parsed-anychar-bar-21 (string-append 0 x0)) ::' rest , 2)
len-dec-rewrite {- P104-} ((Id "P104") :: _::_(InputChar ':') rest) = just (ParseTree (parsed-anychar-bar-22 (string-append 0 (char-to-string ':'))) ::' rest , 2)
len-dec-rewrite {- P105-} ((Id "P105") :: _::_(ParseTree (parsed-anychar-bar-21 x0)) rest) = just (ParseTree (parsed-anychar-bar-22 (string-append 0 x0)) ::' rest , 2)
len-dec-rewrite {- P106-} ((Id "P106") :: _::_(InputChar ')') rest) = just (ParseTree (parsed-anychar-bar-23 (string-append 0 (char-to-string ')'))) ::' rest , 2)
len-dec-rewrite {- P107-} ((Id "P107") :: _::_(ParseTree (parsed-anychar-bar-22 x0)) rest) = just (ParseTree (parsed-anychar-bar-23 (string-append 0 x0)) ::' rest , 2)
len-dec-rewrite {- P108-} ((Id "P108") :: _::_(InputChar '(') rest) = just (ParseTree (parsed-anychar-bar-24 (string-append 0 (char-to-string '('))) ::' rest , 2)
len-dec-rewrite {- P109-} ((Id "P109") :: _::_(ParseTree (parsed-anychar-bar-23 x0)) rest) = just (ParseTree (parsed-anychar-bar-24 (string-append 0 x0)) ::' rest , 2)
len-dec-rewrite {- P11-} ((Id "P11") :: _::_(InputChar 'h') rest) = just (ParseTree (parsed-alpha-range-2 (string-append 0 (char-to-string 'h'))) ::' rest , 2)
len-dec-rewrite {- P110-} ((Id "P110") :: _::_(InputChar '%') rest) = just (ParseTree (parsed-anychar-bar-25 (string-append 0 (char-to-string '%'))) ::' rest , 2)
len-dec-rewrite {- P111-} ((Id "P111") :: _::_(ParseTree (parsed-anychar-bar-24 x0)) rest) = just (ParseTree (parsed-anychar-bar-25 (string-append 0 x0)) ::' rest , 2)
len-dec-rewrite {- P112-} ((Id "P112") :: _::_(InputChar ' ') rest) = just (ParseTree (parsed-anychar-bar-26 (string-append 0 (char-to-string ' '))) ::' rest , 2)
len-dec-rewrite {- P113-} ((Id "P113") :: _::_(ParseTree (parsed-anychar-bar-25 x0)) rest) = just (ParseTree (parsed-anychar-bar-26 (string-append 0 x0)) ::' rest , 2)
len-dec-rewrite {- P114-} ((Id "P114") :: _::_(InputChar '\t') rest) = just (ParseTree (parsed-anychar-bar-27 (string-append 0 (char-to-string '\t'))) ::' rest , 2)
len-dec-rewrite {- P115-} ((Id "P115") :: _::_(ParseTree (parsed-anychar-bar-26 x0)) rest) = just (ParseTree (parsed-anychar-bar-27 (string-append 0 x0)) ::' rest , 2)
len-dec-rewrite {- P116-} ((Id "P116") :: _::_(ParseTree (parsed-numpunct x0)) rest) = just (ParseTree (parsed-anychar-bar-28 (string-append 0 x0)) ::' rest , 2)
len-dec-rewrite {- P117-} ((Id "P117") :: _::_(ParseTree (parsed-anychar-bar-27 x0)) rest) = just (ParseTree (parsed-anychar-bar-28 (string-append 0 x0)) ::' rest , 2)
len-dec-rewrite {- P118-} ((Id "P118") :: _::_(ParseTree (parsed-alpha x0)) rest) = just (ParseTree (parsed-anychar-bar-29 (string-append 0 x0)) ::' rest , 2)
len-dec-rewrite {- P119-} ((Id "P119") :: _::_(ParseTree (parsed-anychar-bar-28 x0)) rest) = just (ParseTree (parsed-anychar-bar-29 (string-append 0 x0)) ::' rest , 2)
len-dec-rewrite {- P12-} ((Id "P12") :: _::_(InputChar 'i') rest) = just (ParseTree (parsed-alpha-range-2 (string-append 0 (char-to-string 'i'))) ::' rest , 2)
len-dec-rewrite {- P120-} ((Id "P120") :: _::_(ParseTree (parsed-anychar-bar-29 x0)) rest) = just (ParseTree (parsed-anychar (string-append 0 x0)) ::' rest , 2)
len-dec-rewrite {- P122-} ((Id "P122") :: (ParseTree (parsed-anychar x0)) :: _::_(ParseTree parsed-comment-star-30) rest) = just (ParseTree parsed-comment-star-30 ::' rest , 3)
len-dec-rewrite {- P123-} ((Id "P123") :: (InputChar '%') :: (ParseTree parsed-comment-star-30) :: _::_(InputChar '\n') rest) = just (ParseTree parsed-comment ::' rest , 4)
len-dec-rewrite {- P124-} ((Id "P124") :: _::_(InputChar ' ') rest) = just (ParseTree parsed-aws-bar-31 ::' rest , 2)
len-dec-rewrite {- P125-} ((Id "P125") :: _::_(ParseTree parsed-comment) rest) = just (ParseTree parsed-aws-bar-31 ::' rest , 2)
len-dec-rewrite {- P126-} ((Id "P126") :: _::_(InputChar '\t') rest) = just (ParseTree parsed-aws-bar-32 ::' rest , 2)
len-dec-rewrite {- P127-} ((Id "P127") :: _::_(ParseTree parsed-aws-bar-31) rest) = just (ParseTree parsed-aws-bar-32 ::' rest , 2)
len-dec-rewrite {- P128-} ((Id "P128") :: _::_(InputChar '\n') rest) = just (ParseTree parsed-aws-bar-33 ::' rest , 2)
len-dec-rewrite {- P129-} ((Id "P129") :: _::_(ParseTree parsed-aws-bar-32) rest) = just (ParseTree parsed-aws-bar-33 ::' rest , 2)
len-dec-rewrite {- P13-} ((Id "P13") :: _::_(InputChar 'j') rest) = just (ParseTree (parsed-alpha-range-2 (string-append 0 (char-to-string 'j'))) ::' rest , 2)
len-dec-rewrite {- P130-} ((Id "P130") :: _::_(ParseTree parsed-aws-bar-33) rest) = just (ParseTree parsed-aws ::' rest , 2)
len-dec-rewrite {- P131-} ((Id "P131") :: _::_(ParseTree parsed-aws) rest) = just (ParseTree parsed-ws-plus-34 ::' rest , 2)
len-dec-rewrite {- P132-} ((Id "P132") :: (ParseTree parsed-aws) :: _::_(ParseTree parsed-ws-plus-34) rest) = just (ParseTree parsed-ws-plus-34 ::' rest , 3)
len-dec-rewrite {- P133-} ((Id "P133") :: _::_(ParseTree parsed-ws-plus-34) rest) = just (ParseTree parsed-ws ::' rest , 2)
len-dec-rewrite {- P135-} ((Id "P135") :: (ParseTree parsed-aws) :: _::_(ParseTree parsed-ows-star-35) rest) = just (ParseTree parsed-ows-star-35 ::' rest , 3)
len-dec-rewrite {- P136-} ((Id "P136") :: _::_(ParseTree parsed-ows-star-35) rest) = just (ParseTree parsed-ows ::' rest , 2)
len-dec-rewrite {- P14-} ((Id "P14") :: _::_(InputChar 'k') rest) = just (ParseTree (parsed-alpha-range-2 (string-append 0 (char-to-string 'k'))) ::' rest , 2)
len-dec-rewrite {- P15-} ((Id "P15") :: _::_(InputChar 'l') rest) = just (ParseTree (parsed-alpha-range-2 (string-append 0 (char-to-string 'l'))) ::' rest , 2)
len-dec-rewrite {- P16-} ((Id "P16") :: _::_(InputChar 'm') rest) = just (ParseTree (parsed-alpha-range-2 (string-append 0 (char-to-string 'm'))) ::' rest , 2)
len-dec-rewrite {- P17-} ((Id "P17") :: _::_(InputChar 'n') rest) = just (ParseTree (parsed-alpha-range-2 (string-append 0 (char-to-string 'n'))) ::' rest , 2)
len-dec-rewrite {- P18-} ((Id "P18") :: _::_(InputChar 'o') rest) = just (ParseTree (parsed-alpha-range-2 (string-append 0 (char-to-string 'o'))) ::' rest , 2)
len-dec-rewrite {- P19-} ((Id "P19") :: _::_(InputChar 'p') rest) = just (ParseTree (parsed-alpha-range-2 (string-append 0 (char-to-string 'p'))) ::' rest , 2)
len-dec-rewrite {- P2-} ((Id "P2") :: (ParseTree (parsed-anychar x0)) :: _::_(ParseTree (parsed-path-star-1 x1)) rest) = just (ParseTree (parsed-path-star-1 (string-append 1 x0 x1)) ::' rest , 3)
len-dec-rewrite {- P20-} ((Id "P20") :: _::_(InputChar 'q') rest) = just (ParseTree (parsed-alpha-range-2 (string-append 0 (char-to-string 'q'))) ::' rest , 2)
len-dec-rewrite {- P21-} ((Id "P21") :: _::_(InputChar 'r') rest) = just (ParseTree (parsed-alpha-range-2 (string-append 0 (char-to-string 'r'))) ::' rest , 2)
len-dec-rewrite {- P22-} ((Id "P22") :: _::_(InputChar 's') rest) = just (ParseTree (parsed-alpha-range-2 (string-append 0 (char-to-string 's'))) ::' rest , 2)
len-dec-rewrite {- P23-} ((Id "P23") :: _::_(InputChar 't') rest) = just (ParseTree (parsed-alpha-range-2 (string-append 0 (char-to-string 't'))) ::' rest , 2)
len-dec-rewrite {- P24-} ((Id "P24") :: _::_(InputChar 'u') rest) = just (ParseTree (parsed-alpha-range-2 (string-append 0 (char-to-string 'u'))) ::' rest , 2)
len-dec-rewrite {- P25-} ((Id "P25") :: _::_(InputChar 'v') rest) = just (ParseTree (parsed-alpha-range-2 (string-append 0 (char-to-string 'v'))) ::' rest , 2)
len-dec-rewrite {- P26-} ((Id "P26") :: _::_(InputChar 'w') rest) = just (ParseTree (parsed-alpha-range-2 (string-append 0 (char-to-string 'w'))) ::' rest , 2)
len-dec-rewrite {- P27-} ((Id "P27") :: _::_(InputChar 'x') rest) = just (ParseTree (parsed-alpha-range-2 (string-append 0 (char-to-string 'x'))) ::' rest , 2)
len-dec-rewrite {- P28-} ((Id "P28") :: _::_(InputChar 'y') rest) = just (ParseTree (parsed-alpha-range-2 (string-append 0 (char-to-string 'y'))) ::' rest , 2)
len-dec-rewrite {- P29-} ((Id "P29") :: _::_(InputChar 'z') rest) = just (ParseTree (parsed-alpha-range-2 (string-append 0 (char-to-string 'z'))) ::' rest , 2)
len-dec-rewrite {- P3-} ((Id "P3") :: (ParseTree parsed-squote) :: (ParseTree (parsed-path-star-1 x0)) :: _::_(ParseTree parsed-squote) rest) = just (ParseTree (parsed-path (string-append 0 x0)) ::' rest , 4)
len-dec-rewrite {- P30-} ((Id "P30") :: _::_(InputChar 'A') rest) = just (ParseTree (parsed-alpha-range-3 (string-append 0 (char-to-string 'A'))) ::' rest , 2)
len-dec-rewrite {- P31-} ((Id "P31") :: _::_(InputChar 'B') rest) = just (ParseTree (parsed-alpha-range-3 (string-append 0 (char-to-string 'B'))) ::' rest , 2)
len-dec-rewrite {- P32-} ((Id "P32") :: _::_(InputChar 'C') rest) = just (ParseTree (parsed-alpha-range-3 (string-append 0 (char-to-string 'C'))) ::' rest , 2)
len-dec-rewrite {- P33-} ((Id "P33") :: _::_(InputChar 'D') rest) = just (ParseTree (parsed-alpha-range-3 (string-append 0 (char-to-string 'D'))) ::' rest , 2)
len-dec-rewrite {- P34-} ((Id "P34") :: _::_(InputChar 'E') rest) = just (ParseTree (parsed-alpha-range-3 (string-append 0 (char-to-string 'E'))) ::' rest , 2)
len-dec-rewrite {- P35-} ((Id "P35") :: _::_(InputChar 'F') rest) = just (ParseTree (parsed-alpha-range-3 (string-append 0 (char-to-string 'F'))) ::' rest , 2)
len-dec-rewrite {- P36-} ((Id "P36") :: _::_(InputChar 'G') rest) = just (ParseTree (parsed-alpha-range-3 (string-append 0 (char-to-string 'G'))) ::' rest , 2)
len-dec-rewrite {- P37-} ((Id "P37") :: _::_(InputChar 'H') rest) = just (ParseTree (parsed-alpha-range-3 (string-append 0 (char-to-string 'H'))) ::' rest , 2)
len-dec-rewrite {- P38-} ((Id "P38") :: _::_(InputChar 'I') rest) = just (ParseTree (parsed-alpha-range-3 (string-append 0 (char-to-string 'I'))) ::' rest , 2)
len-dec-rewrite {- P39-} ((Id "P39") :: _::_(InputChar 'J') rest) = just (ParseTree (parsed-alpha-range-3 (string-append 0 (char-to-string 'J'))) ::' rest , 2)
len-dec-rewrite {- P4-} ((Id "P4") :: _::_(InputChar 'a') rest) = just (ParseTree (parsed-alpha-range-2 (string-append 0 (char-to-string 'a'))) ::' rest , 2)
len-dec-rewrite {- P40-} ((Id "P40") :: _::_(InputChar 'K') rest) = just (ParseTree (parsed-alpha-range-3 (string-append 0 (char-to-string 'K'))) ::' rest , 2)
len-dec-rewrite {- P41-} ((Id "P41") :: _::_(InputChar 'L') rest) = just (ParseTree (parsed-alpha-range-3 (string-append 0 (char-to-string 'L'))) ::' rest , 2)
len-dec-rewrite {- P42-} ((Id "P42") :: _::_(InputChar 'M') rest) = just (ParseTree (parsed-alpha-range-3 (string-append 0 (char-to-string 'M'))) ::' rest , 2)
len-dec-rewrite {- P43-} ((Id "P43") :: _::_(InputChar 'N') rest) = just (ParseTree (parsed-alpha-range-3 (string-append 0 (char-to-string 'N'))) ::' rest , 2)
len-dec-rewrite {- P44-} ((Id "P44") :: _::_(InputChar 'O') rest) = just (ParseTree (parsed-alpha-range-3 (string-append 0 (char-to-string 'O'))) ::' rest , 2)
len-dec-rewrite {- P45-} ((Id "P45") :: _::_(InputChar 'P') rest) = just (ParseTree (parsed-alpha-range-3 (string-append 0 (char-to-string 'P'))) ::' rest , 2)
len-dec-rewrite {- P46-} ((Id "P46") :: _::_(InputChar 'Q') rest) = just (ParseTree (parsed-alpha-range-3 (string-append 0 (char-to-string 'Q'))) ::' rest , 2)
len-dec-rewrite {- P47-} ((Id "P47") :: _::_(InputChar 'R') rest) = just (ParseTree (parsed-alpha-range-3 (string-append 0 (char-to-string 'R'))) ::' rest , 2)
len-dec-rewrite {- P48-} ((Id "P48") :: _::_(InputChar 'S') rest) = just (ParseTree (parsed-alpha-range-3 (string-append 0 (char-to-string 'S'))) ::' rest , 2)
len-dec-rewrite {- P49-} ((Id "P49") :: _::_(InputChar 'T') rest) = just (ParseTree (parsed-alpha-range-3 (string-append 0 (char-to-string 'T'))) ::' rest , 2)
len-dec-rewrite {- P5-} ((Id "P5") :: _::_(InputChar 'b') rest) = just (ParseTree (parsed-alpha-range-2 (string-append 0 (char-to-string 'b'))) ::' rest , 2)
len-dec-rewrite {- P50-} ((Id "P50") :: _::_(InputChar 'U') rest) = just (ParseTree (parsed-alpha-range-3 (string-append 0 (char-to-string 'U'))) ::' rest , 2)
len-dec-rewrite {- P51-} ((Id "P51") :: _::_(InputChar 'V') rest) = just (ParseTree (parsed-alpha-range-3 (string-append 0 (char-to-string 'V'))) ::' rest , 2)
len-dec-rewrite {- P52-} ((Id "P52") :: _::_(InputChar 'W') rest) = just (ParseTree (parsed-alpha-range-3 (string-append 0 (char-to-string 'W'))) ::' rest , 2)
len-dec-rewrite {- P53-} ((Id "P53") :: _::_(InputChar 'X') rest) = just (ParseTree (parsed-alpha-range-3 (string-append 0 (char-to-string 'X'))) ::' rest , 2)
len-dec-rewrite {- P54-} ((Id "P54") :: _::_(InputChar 'Y') rest) = just (ParseTree (parsed-alpha-range-3 (string-append 0 (char-to-string 'Y'))) ::' rest , 2)
len-dec-rewrite {- P55-} ((Id "P55") :: _::_(InputChar 'Z') rest) = just (ParseTree (parsed-alpha-range-3 (string-append 0 (char-to-string 'Z'))) ::' rest , 2)
len-dec-rewrite {- P56-} ((Id "P56") :: _::_(ParseTree (parsed-alpha-range-2 x0)) rest) = just (ParseTree (parsed-alpha-bar-4 (string-append 0 x0)) ::' rest , 2)
len-dec-rewrite {- P57-} ((Id "P57") :: _::_(ParseTree (parsed-alpha-range-3 x0)) rest) = just (ParseTree (parsed-alpha-bar-4 (string-append 0 x0)) ::' rest , 2)
len-dec-rewrite {- P58-} ((Id "P58") :: _::_(ParseTree (parsed-alpha-bar-4 x0)) rest) = just (ParseTree (parsed-alpha (string-append 0 x0)) ::' rest , 2)
len-dec-rewrite {- P59-} ((Id "P59") :: _::_(InputChar '0') rest) = just (ParseTree (parsed-numone-range-5 (string-append 0 (char-to-string '0'))) ::' rest , 2)
len-dec-rewrite {- P6-} ((Id "P6") :: _::_(InputChar 'c') rest) = just (ParseTree (parsed-alpha-range-2 (string-append 0 (char-to-string 'c'))) ::' rest , 2)
len-dec-rewrite {- P60-} ((Id "P60") :: _::_(InputChar '1') rest) = just (ParseTree (parsed-numone-range-5 (string-append 0 (char-to-string '1'))) ::' rest , 2)
len-dec-rewrite {- P61-} ((Id "P61") :: _::_(InputChar '2') rest) = just (ParseTree (parsed-numone-range-5 (string-append 0 (char-to-string '2'))) ::' rest , 2)
len-dec-rewrite {- P62-} ((Id "P62") :: _::_(InputChar '3') rest) = just (ParseTree (parsed-numone-range-5 (string-append 0 (char-to-string '3'))) ::' rest , 2)
len-dec-rewrite {- P63-} ((Id "P63") :: _::_(InputChar '4') rest) = just (ParseTree (parsed-numone-range-5 (string-append 0 (char-to-string '4'))) ::' rest , 2)
len-dec-rewrite {- P64-} ((Id "P64") :: _::_(InputChar '5') rest) = just (ParseTree (parsed-numone-range-5 (string-append 0 (char-to-string '5'))) ::' rest , 2)
len-dec-rewrite {- P65-} ((Id "P65") :: _::_(InputChar '6') rest) = just (ParseTree (parsed-numone-range-5 (string-append 0 (char-to-string '6'))) ::' rest , 2)
len-dec-rewrite {- P66-} ((Id "P66") :: _::_(InputChar '7') rest) = just (ParseTree (parsed-numone-range-5 (string-append 0 (char-to-string '7'))) ::' rest , 2)
len-dec-rewrite {- P67-} ((Id "P67") :: _::_(InputChar '8') rest) = just (ParseTree (parsed-numone-range-5 (string-append 0 (char-to-string '8'))) ::' rest , 2)
len-dec-rewrite {- P68-} ((Id "P68") :: _::_(InputChar '9') rest) = just (ParseTree (parsed-numone-range-5 (string-append 0 (char-to-string '9'))) ::' rest , 2)
len-dec-rewrite {- P69-} ((Id "P69") :: _::_(ParseTree (parsed-numone-range-5 x0)) rest) = just (ParseTree (parsed-numone (string-append 0 x0)) ::' rest , 2)
len-dec-rewrite {- P7-} ((Id "P7") :: _::_(InputChar 'd') rest) = just (ParseTree (parsed-alpha-range-2 (string-append 0 (char-to-string 'd'))) ::' rest , 2)
len-dec-rewrite {- P70-} ((Id "P70") :: _::_(ParseTree (parsed-numone x0)) rest) = just (ParseTree (parsed-num-plus-6 (string-append 0 x0)) ::' rest , 2)
len-dec-rewrite {- P71-} ((Id "P71") :: (ParseTree (parsed-numone x0)) :: _::_(ParseTree (parsed-num-plus-6 x1)) rest) = just (ParseTree (parsed-num-plus-6 (string-append 1 x0 x1)) ::' rest , 3)
len-dec-rewrite {- P72-} ((Id "P72") :: _::_(ParseTree (parsed-num-plus-6 x0)) rest) = just (ParseTree (parsed-num (string-append 0 x0)) ::' rest , 2)
len-dec-rewrite {- P73-} ((Id "P73") :: _::_(InputChar '\'') rest) = just (ParseTree (parsed-numpunct-bar-7 (string-append 0 (char-to-string '\''))) ::' rest , 2)
len-dec-rewrite {- P74-} ((Id "P74") :: _::_(InputChar '-') rest) = just (ParseTree (parsed-numpunct-bar-7 (string-append 0 (char-to-string '-'))) ::' rest , 2)
len-dec-rewrite {- P75-} ((Id "P75") :: _::_(ParseTree (parsed-numone x0)) rest) = just (ParseTree (parsed-numpunct-bar-8 (string-append 0 x0)) ::' rest , 2)
len-dec-rewrite {- P76-} ((Id "P76") :: _::_(ParseTree (parsed-numpunct-bar-7 x0)) rest) = just (ParseTree (parsed-numpunct-bar-8 (string-append 0 x0)) ::' rest , 2)
len-dec-rewrite {- P77-} ((Id "P77") :: _::_(ParseTree (parsed-numpunct-bar-8 x0)) rest) = just (ParseTree (parsed-numpunct (string-append 0 x0)) ::' rest , 2)
len-dec-rewrite {- P78-} ((Id "P78") :: _::_(InputChar '/') rest) = just (ParseTree (parsed-anychar-bar-9 (string-append 0 (char-to-string '/'))) ::' rest , 2)
len-dec-rewrite {- P79-} ((Id "P79") :: _::_(InputChar '_') rest) = just (ParseTree (parsed-anychar-bar-9 (string-append 0 (char-to-string '_'))) ::' rest , 2)
len-dec-rewrite {- P8-} ((Id "P8") :: _::_(InputChar 'e') rest) = just (ParseTree (parsed-alpha-range-2 (string-append 0 (char-to-string 'e'))) ::' rest , 2)
len-dec-rewrite {- P80-} ((Id "P80") :: _::_(InputChar '>') rest) = just (ParseTree (parsed-anychar-bar-10 (string-append 0 (char-to-string '>'))) ::' rest , 2)
len-dec-rewrite {- P81-} ((Id "P81") :: _::_(ParseTree (parsed-anychar-bar-9 x0)) rest) = just (ParseTree (parsed-anychar-bar-10 (string-append 0 x0)) ::' rest , 2)
len-dec-rewrite {- P82-} ((Id "P82") :: _::_(InputChar '<') rest) = just (ParseTree (parsed-anychar-bar-11 (string-append 0 (char-to-string '<'))) ::' rest , 2)
len-dec-rewrite {- P83-} ((Id "P83") :: _::_(ParseTree (parsed-anychar-bar-10 x0)) rest) = just (ParseTree (parsed-anychar-bar-11 (string-append 0 x0)) ::' rest , 2)
len-dec-rewrite {- P84-} ((Id "P84") :: _::_(InputChar '+') rest) = just (ParseTree (parsed-anychar-bar-12 (string-append 0 (char-to-string '+'))) ::' rest , 2)
len-dec-rewrite {- P85-} ((Id "P85") :: _::_(ParseTree (parsed-anychar-bar-11 x0)) rest) = just (ParseTree (parsed-anychar-bar-12 (string-append 0 x0)) ::' rest , 2)
len-dec-rewrite {- P86-} ((Id "P86") :: _::_(InputChar '=') rest) = just (ParseTree (parsed-anychar-bar-13 (string-append 0 (char-to-string '='))) ::' rest , 2)
len-dec-rewrite {- P87-} ((Id "P87") :: _::_(ParseTree (parsed-anychar-bar-12 x0)) rest) = just (ParseTree (parsed-anychar-bar-13 (string-append 0 x0)) ::' rest , 2)
len-dec-rewrite {- P88-} ((Id "P88") :: _::_(InputChar '-') rest) = just (ParseTree (parsed-anychar-bar-14 (string-append 0 (char-to-string '-'))) ::' rest , 2)
len-dec-rewrite {- P89-} ((Id "P89") :: _::_(ParseTree (parsed-anychar-bar-13 x0)) rest) = just (ParseTree (parsed-anychar-bar-14 (string-append 0 x0)) ::' rest , 2)
len-dec-rewrite {- P9-} ((Id "P9") :: _::_(InputChar 'f') rest) = just (ParseTree (parsed-alpha-range-2 (string-append 0 (char-to-string 'f'))) ::' rest , 2)
len-dec-rewrite {- P90-} ((Id "P90") :: _::_(InputChar '}') rest) = just (ParseTree (parsed-anychar-bar-15 (string-append 0 (char-to-string '}'))) ::' rest , 2)
len-dec-rewrite {- P91-} ((Id "P91") :: _::_(ParseTree (parsed-anychar-bar-14 x0)) rest) = just (ParseTree (parsed-anychar-bar-15 (string-append 0 x0)) ::' rest , 2)
len-dec-rewrite {- P92-} ((Id "P92") :: _::_(InputChar '{') rest) = just (ParseTree (parsed-anychar-bar-16 (string-append 0 (char-to-string '{'))) ::' rest , 2)
len-dec-rewrite {- P93-} ((Id "P93") :: _::_(ParseTree (parsed-anychar-bar-15 x0)) rest) = just (ParseTree (parsed-anychar-bar-16 (string-append 0 x0)) ::' rest , 2)
len-dec-rewrite {- P94-} ((Id "P94") :: _::_(InputChar '!') rest) = just (ParseTree (parsed-anychar-bar-17 (string-append 0 (char-to-string '!'))) ::' rest , 2)
len-dec-rewrite {- P95-} ((Id "P95") :: _::_(ParseTree (parsed-anychar-bar-16 x0)) rest) = just (ParseTree (parsed-anychar-bar-17 (string-append 0 x0)) ::' rest , 2)
len-dec-rewrite {- P96-} ((Id "P96") :: _::_(InputChar ',') rest) = just (ParseTree (parsed-anychar-bar-18 (string-append 0 (char-to-string ','))) ::' rest , 2)
len-dec-rewrite {- P97-} ((Id "P97") :: _::_(ParseTree (parsed-anychar-bar-17 x0)) rest) = just (ParseTree (parsed-anychar-bar-18 (string-append 0 x0)) ::' rest , 2)
len-dec-rewrite {- P98-} ((Id "P98") :: _::_(InputChar ']') rest) = just (ParseTree (parsed-anychar-bar-19 (string-append 0 (char-to-string ']'))) ::' rest , 2)
len-dec-rewrite {- P99-} ((Id "P99") :: _::_(ParseTree (parsed-anychar-bar-18 x0)) rest) = just (ParseTree (parsed-anychar-bar-19 (string-append 0 x0)) ::' rest , 2)
len-dec-rewrite {- PathsCons-} ((Id "PathsCons") :: (ParseTree parsed-ws) :: (ParseTree (parsed-path x0)) :: _::_(ParseTree (parsed-paths x1)) rest) = just (ParseTree (parsed-paths (norm-paths (PathsCons x0 x1))) ::' rest , 4)
len-dec-rewrite {- ShowQualifiedVars-} ((Id "ShowQualifiedVars") :: (InputChar 's') :: (InputChar 'h') :: (InputChar 'o') :: (InputChar 'w') :: (InputChar '-') :: (InputChar 'q') :: (InputChar 'u') :: (InputChar 'a') :: (InputChar 'l') :: (InputChar 'i') :: (InputChar 'f') :: (InputChar 'i') :: (InputChar 'e') :: (InputChar 'd') :: (InputChar '-') :: (InputChar 'v') :: (InputChar 'a') :: (InputChar 'r') :: (InputChar 's') :: (ParseTree parsed-ows) :: (InputChar '=') :: (ParseTree parsed-ows) :: (ParseTree (parsed-str-bool x0)) :: (ParseTree parsed-ows) :: (InputChar '.') :: _::_(ParseTree parsed-ows) rest) = just (ParseTree (parsed-opt (norm-opt (ShowQualifiedVars x0))) ::' rest , 27)
len-dec-rewrite {- StrBoolFalse-} ((Id "StrBoolFalse") :: (InputChar 'f') :: (InputChar 'a') :: (InputChar 'l') :: (InputChar 's') :: _::_(InputChar 'e') rest) = just (ParseTree (parsed-str-bool (norm-str-bool StrBoolFalse)) ::' rest , 6)
len-dec-rewrite {- StrBoolTrue-} ((Id "StrBoolTrue") :: (InputChar 't') :: (InputChar 'r') :: (InputChar 'u') :: _::_(InputChar 'e') rest) = just (ParseTree (parsed-str-bool (norm-str-bool StrBoolTrue)) ::' rest , 5)
len-dec-rewrite {- UseCedeFiles-} ((Id "UseCedeFiles") :: (InputChar 'u') :: (InputChar 's') :: (InputChar 'e') :: (InputChar '-') :: (InputChar 'c') :: (InputChar 'e') :: (InputChar 'd') :: (InputChar 'e') :: (InputChar '-') :: (InputChar 'f') :: (InputChar 'i') :: (InputChar 'l') :: (InputChar 'e') :: (InputChar 's') :: (ParseTree parsed-ows) :: (InputChar '=') :: (ParseTree parsed-ows) :: (ParseTree (parsed-str-bool x0)) :: (ParseTree parsed-ows) :: (InputChar '.') :: _::_(ParseTree parsed-ows) rest) = just (ParseTree (parsed-opt (norm-opt (UseCedeFiles x0))) ::' rest , 22)
len-dec-rewrite {- OptsNil-} (_::_(Id "OptsNil") rest) = just (ParseTree (parsed-opts (norm-opts OptsNil)) ::' rest , 1)
len-dec-rewrite {- P1-} (_::_(Id "P1") rest) = just (ParseTree (parsed-path-star-1 empty-string) ::' rest , 1)
len-dec-rewrite {- P121-} (_::_(Id "P121") rest) = just (ParseTree parsed-comment-star-30 ::' rest , 1)
len-dec-rewrite {- P134-} (_::_(Id "P134") rest) = just (ParseTree parsed-ows-star-35 ::' rest , 1)
len-dec-rewrite {- PathsNil-} (_::_(Id "PathsNil") rest) = just (ParseTree (parsed-paths (norm-paths PathsNil)) ::' rest , 1)
len-dec-rewrite {- Posinfo-} (_::_(Posinfo n) rest) = just (ParseTree (parsed-posinfo (ℕ-to-string n)) ::' rest , 1)
len-dec-rewrite x = nothing

rrs : rewriteRules
rrs = record { len-dec-rewrite = len-dec-rewrite }
