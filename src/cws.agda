module cws where

open import lib

open import cws-types public
----------------------------------------------------------------------------------
-- Run-rewriting rules
----------------------------------------------------------------------------------

data gratr2-nt : Set where
  _ws-plus-67 : gratr2-nt
  _ws : gratr2-nt
  _start : gratr2-nt
  _posinfo : gratr2-nt
  _otherpunct-bar-58 : gratr2-nt
  _otherpunct-bar-57 : gratr2-nt
  _otherpunct-bar-56 : gratr2-nt
  _otherpunct-bar-55 : gratr2-nt
  _otherpunct-bar-54 : gratr2-nt
  _otherpunct-bar-53 : gratr2-nt
  _otherpunct-bar-52 : gratr2-nt
  _otherpunct-bar-51 : gratr2-nt
  _otherpunct-bar-50 : gratr2-nt
  _otherpunct-bar-49 : gratr2-nt
  _otherpunct-bar-48 : gratr2-nt
  _otherpunct-bar-47 : gratr2-nt
  _otherpunct-bar-46 : gratr2-nt
  _otherpunct-bar-45 : gratr2-nt
  _otherpunct-bar-44 : gratr2-nt
  _otherpunct-bar-43 : gratr2-nt
  _otherpunct-bar-42 : gratr2-nt
  _otherpunct-bar-41 : gratr2-nt
  _otherpunct-bar-40 : gratr2-nt
  _otherpunct-bar-39 : gratr2-nt
  _otherpunct-bar-38 : gratr2-nt
  _otherpunct-bar-37 : gratr2-nt
  _otherpunct-bar-36 : gratr2-nt
  _otherpunct-bar-35 : gratr2-nt
  _otherpunct-bar-34 : gratr2-nt
  _otherpunct-bar-33 : gratr2-nt
  _otherpunct-bar-32 : gratr2-nt
  _otherpunct-bar-31 : gratr2-nt
  _otherpunct-bar-30 : gratr2-nt
  _otherpunct-bar-29 : gratr2-nt
  _otherpunct-bar-28 : gratr2-nt
  _otherpunct-bar-27 : gratr2-nt
  _otherpunct-bar-26 : gratr2-nt
  _otherpunct-bar-25 : gratr2-nt
  _otherpunct-bar-24 : gratr2-nt
  _otherpunct-bar-23 : gratr2-nt
  _otherpunct-bar-22 : gratr2-nt
  _otherpunct-bar-21 : gratr2-nt
  _otherpunct-bar-20 : gratr2-nt
  _otherpunct-bar-19 : gratr2-nt
  _otherpunct-bar-18 : gratr2-nt
  _otherpunct-bar-17 : gratr2-nt
  _otherpunct-bar-16 : gratr2-nt
  _otherpunct-bar-15 : gratr2-nt
  _otherpunct-bar-14 : gratr2-nt
  _otherpunct-bar-13 : gratr2-nt
  _otherpunct-bar-12 : gratr2-nt
  _otherpunct : gratr2-nt
  _numpunct-bar-9 : gratr2-nt
  _numpunct-bar-8 : gratr2-nt
  _numpunct-bar-7 : gratr2-nt
  _numpunct-bar-6 : gratr2-nt
  _numpunct-bar-11 : gratr2-nt
  _numpunct-bar-10 : gratr2-nt
  _numpunct : gratr2-nt
  _numone-range-4 : gratr2-nt
  _numone : gratr2-nt
  _num-plus-5 : gratr2-nt
  _num : gratr2-nt
  _nonws-plus-70 : gratr2-nt
  _nonws : gratr2-nt
  _entity : gratr2-nt
  _entities : gratr2-nt
  _comment-star-64 : gratr2-nt
  _comment : gratr2-nt
  _aws-bar-66 : gratr2-nt
  _aws-bar-65 : gratr2-nt
  _aws : gratr2-nt
  _anynonwschar-bar-69 : gratr2-nt
  _anynonwschar-bar-68 : gratr2-nt
  _anynonwschar : gratr2-nt
  _anychar-bar-63 : gratr2-nt
  _anychar-bar-62 : gratr2-nt
  _anychar-bar-61 : gratr2-nt
  _anychar-bar-60 : gratr2-nt
  _anychar-bar-59 : gratr2-nt
  _anychar : gratr2-nt
  _alpha-range-2 : gratr2-nt
  _alpha-range-1 : gratr2-nt
  _alpha-bar-3 : gratr2-nt
  _alpha : gratr2-nt


gratr2-nt-eq : gratr2-nt → gratr2-nt → 𝔹
gratr2-nt-eq  _ws-plus-67 _ws-plus-67 = tt
gratr2-nt-eq  _ws _ws = tt
gratr2-nt-eq  _start _start = tt
gratr2-nt-eq  _posinfo _posinfo = tt
gratr2-nt-eq  _otherpunct-bar-58 _otherpunct-bar-58 = tt
gratr2-nt-eq  _otherpunct-bar-57 _otherpunct-bar-57 = tt
gratr2-nt-eq  _otherpunct-bar-56 _otherpunct-bar-56 = tt
gratr2-nt-eq  _otherpunct-bar-55 _otherpunct-bar-55 = tt
gratr2-nt-eq  _otherpunct-bar-54 _otherpunct-bar-54 = tt
gratr2-nt-eq  _otherpunct-bar-53 _otherpunct-bar-53 = tt
gratr2-nt-eq  _otherpunct-bar-52 _otherpunct-bar-52 = tt
gratr2-nt-eq  _otherpunct-bar-51 _otherpunct-bar-51 = tt
gratr2-nt-eq  _otherpunct-bar-50 _otherpunct-bar-50 = tt
gratr2-nt-eq  _otherpunct-bar-49 _otherpunct-bar-49 = tt
gratr2-nt-eq  _otherpunct-bar-48 _otherpunct-bar-48 = tt
gratr2-nt-eq  _otherpunct-bar-47 _otherpunct-bar-47 = tt
gratr2-nt-eq  _otherpunct-bar-46 _otherpunct-bar-46 = tt
gratr2-nt-eq  _otherpunct-bar-45 _otherpunct-bar-45 = tt
gratr2-nt-eq  _otherpunct-bar-44 _otherpunct-bar-44 = tt
gratr2-nt-eq  _otherpunct-bar-43 _otherpunct-bar-43 = tt
gratr2-nt-eq  _otherpunct-bar-42 _otherpunct-bar-42 = tt
gratr2-nt-eq  _otherpunct-bar-41 _otherpunct-bar-41 = tt
gratr2-nt-eq  _otherpunct-bar-40 _otherpunct-bar-40 = tt
gratr2-nt-eq  _otherpunct-bar-39 _otherpunct-bar-39 = tt
gratr2-nt-eq  _otherpunct-bar-38 _otherpunct-bar-38 = tt
gratr2-nt-eq  _otherpunct-bar-37 _otherpunct-bar-37 = tt
gratr2-nt-eq  _otherpunct-bar-36 _otherpunct-bar-36 = tt
gratr2-nt-eq  _otherpunct-bar-35 _otherpunct-bar-35 = tt
gratr2-nt-eq  _otherpunct-bar-34 _otherpunct-bar-34 = tt
gratr2-nt-eq  _otherpunct-bar-33 _otherpunct-bar-33 = tt
gratr2-nt-eq  _otherpunct-bar-32 _otherpunct-bar-32 = tt
gratr2-nt-eq  _otherpunct-bar-31 _otherpunct-bar-31 = tt
gratr2-nt-eq  _otherpunct-bar-30 _otherpunct-bar-30 = tt
gratr2-nt-eq  _otherpunct-bar-29 _otherpunct-bar-29 = tt
gratr2-nt-eq  _otherpunct-bar-28 _otherpunct-bar-28 = tt
gratr2-nt-eq  _otherpunct-bar-27 _otherpunct-bar-27 = tt
gratr2-nt-eq  _otherpunct-bar-26 _otherpunct-bar-26 = tt
gratr2-nt-eq  _otherpunct-bar-25 _otherpunct-bar-25 = tt
gratr2-nt-eq  _otherpunct-bar-24 _otherpunct-bar-24 = tt
gratr2-nt-eq  _otherpunct-bar-23 _otherpunct-bar-23 = tt
gratr2-nt-eq  _otherpunct-bar-22 _otherpunct-bar-22 = tt
gratr2-nt-eq  _otherpunct-bar-21 _otherpunct-bar-21 = tt
gratr2-nt-eq  _otherpunct-bar-20 _otherpunct-bar-20 = tt
gratr2-nt-eq  _otherpunct-bar-19 _otherpunct-bar-19 = tt
gratr2-nt-eq  _otherpunct-bar-18 _otherpunct-bar-18 = tt
gratr2-nt-eq  _otherpunct-bar-17 _otherpunct-bar-17 = tt
gratr2-nt-eq  _otherpunct-bar-16 _otherpunct-bar-16 = tt
gratr2-nt-eq  _otherpunct-bar-15 _otherpunct-bar-15 = tt
gratr2-nt-eq  _otherpunct-bar-14 _otherpunct-bar-14 = tt
gratr2-nt-eq  _otherpunct-bar-13 _otherpunct-bar-13 = tt
gratr2-nt-eq  _otherpunct-bar-12 _otherpunct-bar-12 = tt
gratr2-nt-eq  _otherpunct _otherpunct = tt
gratr2-nt-eq  _numpunct-bar-9 _numpunct-bar-9 = tt
gratr2-nt-eq  _numpunct-bar-8 _numpunct-bar-8 = tt
gratr2-nt-eq  _numpunct-bar-7 _numpunct-bar-7 = tt
gratr2-nt-eq  _numpunct-bar-6 _numpunct-bar-6 = tt
gratr2-nt-eq  _numpunct-bar-11 _numpunct-bar-11 = tt
gratr2-nt-eq  _numpunct-bar-10 _numpunct-bar-10 = tt
gratr2-nt-eq  _numpunct _numpunct = tt
gratr2-nt-eq  _numone-range-4 _numone-range-4 = tt
gratr2-nt-eq  _numone _numone = tt
gratr2-nt-eq  _num-plus-5 _num-plus-5 = tt
gratr2-nt-eq  _num _num = tt
gratr2-nt-eq  _nonws-plus-70 _nonws-plus-70 = tt
gratr2-nt-eq  _nonws _nonws = tt
gratr2-nt-eq  _entity _entity = tt
gratr2-nt-eq  _entities _entities = tt
gratr2-nt-eq  _comment-star-64 _comment-star-64 = tt
gratr2-nt-eq  _comment _comment = tt
gratr2-nt-eq  _aws-bar-66 _aws-bar-66 = tt
gratr2-nt-eq  _aws-bar-65 _aws-bar-65 = tt
gratr2-nt-eq  _aws _aws = tt
gratr2-nt-eq  _anynonwschar-bar-69 _anynonwschar-bar-69 = tt
gratr2-nt-eq  _anynonwschar-bar-68 _anynonwschar-bar-68 = tt
gratr2-nt-eq  _anynonwschar _anynonwschar = tt
gratr2-nt-eq  _anychar-bar-63 _anychar-bar-63 = tt
gratr2-nt-eq  _anychar-bar-62 _anychar-bar-62 = tt
gratr2-nt-eq  _anychar-bar-61 _anychar-bar-61 = tt
gratr2-nt-eq  _anychar-bar-60 _anychar-bar-60 = tt
gratr2-nt-eq  _anychar-bar-59 _anychar-bar-59 = tt
gratr2-nt-eq  _anychar _anychar = tt
gratr2-nt-eq  _alpha-range-2 _alpha-range-2 = tt
gratr2-nt-eq  _alpha-range-1 _alpha-range-1 = tt
gratr2-nt-eq  _alpha-bar-3 _alpha-bar-3 = tt
gratr2-nt-eq  _alpha _alpha = tt
gratr2-nt-eq _ _ = ff


open import rtn gratr2-nt


cws-start : gratr2-nt → 𝕃 gratr2-rule
cws-start _ws-plus-67 = (just "P197" , nothing , just _ws-plus-67 , inj₁ _aws :: inj₁ _ws-plus-67 :: []) :: (just "P196" , nothing , just _ws-plus-67 , inj₁ _aws :: []) :: []
cws-start _ws = (just "P198" , nothing , just _ws , inj₁ _ws-plus-67 :: []) :: []
cws-start _start = (just "File" , nothing , just _start , inj₁ _entities :: []) :: []
cws-start _posinfo = (just "Posinfo" , nothing , just _posinfo , []) :: []
cws-start _otherpunct-bar-58 = (just "P175" , nothing , just _otherpunct-bar-58 , inj₁ _otherpunct-bar-57 :: []) :: (just "P174" , nothing , just _otherpunct-bar-58 , inj₂ '|' :: []) :: []
cws-start _otherpunct-bar-57 = (just "P173" , nothing , just _otherpunct-bar-57 , inj₁ _otherpunct-bar-56 :: []) :: (just "P172" , nothing , just _otherpunct-bar-57 , inj₂ '□' :: []) :: []
cws-start _otherpunct-bar-56 = (just "P171" , nothing , just _otherpunct-bar-56 , inj₁ _otherpunct-bar-55 :: []) :: (just "P170" , nothing , just _otherpunct-bar-56 , inj₂ 'Π' :: []) :: []
cws-start _otherpunct-bar-55 = (just "P169" , nothing , just _otherpunct-bar-55 , inj₁ _otherpunct-bar-54 :: []) :: (just "P168" , nothing , just _otherpunct-bar-55 , inj₂ 'ι' :: []) :: []
cws-start _otherpunct-bar-54 = (just "P167" , nothing , just _otherpunct-bar-54 , inj₁ _otherpunct-bar-53 :: []) :: (just "P166" , nothing , just _otherpunct-bar-54 , inj₂ 'λ' :: []) :: []
cws-start _otherpunct-bar-53 = (just "P165" , nothing , just _otherpunct-bar-53 , inj₁ _otherpunct-bar-52 :: []) :: (just "P164" , nothing , just _otherpunct-bar-53 , inj₂ '∀' :: []) :: []
cws-start _otherpunct-bar-52 = (just "P163" , nothing , just _otherpunct-bar-52 , inj₁ _otherpunct-bar-51 :: []) :: (just "P162" , nothing , just _otherpunct-bar-52 , inj₂ 'π' :: []) :: []
cws-start _otherpunct-bar-51 = (just "P161" , nothing , just _otherpunct-bar-51 , inj₁ _otherpunct-bar-50 :: []) :: (just "P160" , nothing , just _otherpunct-bar-51 , inj₂ '★' :: []) :: []
cws-start _otherpunct-bar-50 = (just "P159" , nothing , just _otherpunct-bar-50 , inj₁ _otherpunct-bar-49 :: []) :: (just "P158" , nothing , just _otherpunct-bar-50 , inj₂ '☆' :: []) :: []
cws-start _otherpunct-bar-49 = (just "P157" , nothing , just _otherpunct-bar-49 , inj₁ _otherpunct-bar-48 :: []) :: (just "P156" , nothing , just _otherpunct-bar-49 , inj₂ '·' :: []) :: []
cws-start _otherpunct-bar-48 = (just "P155" , nothing , just _otherpunct-bar-48 , inj₁ _otherpunct-bar-47 :: []) :: (just "P154" , nothing , just _otherpunct-bar-48 , inj₂ '⇐' :: []) :: []
cws-start _otherpunct-bar-47 = (just "P153" , nothing , just _otherpunct-bar-47 , inj₁ _otherpunct-bar-46 :: []) :: (just "P152" , nothing , just _otherpunct-bar-47 , inj₂ '➔' :: []) :: []
cws-start _otherpunct-bar-46 = (just "P151" , nothing , just _otherpunct-bar-46 , inj₁ _otherpunct-bar-45 :: []) :: (just "P150" , nothing , just _otherpunct-bar-46 , inj₂ '➾' :: []) :: []
cws-start _otherpunct-bar-45 = (just "P149" , nothing , just _otherpunct-bar-45 , inj₁ _otherpunct-bar-44 :: []) :: (just "P148" , nothing , just _otherpunct-bar-45 , inj₂ '↑' :: []) :: []
cws-start _otherpunct-bar-44 = (just "P147" , nothing , just _otherpunct-bar-44 , inj₁ _otherpunct-bar-43 :: []) :: (just "P146" , nothing , just _otherpunct-bar-44 , inj₂ '●' :: []) :: []
cws-start _otherpunct-bar-43 = (just "P145" , nothing , just _otherpunct-bar-43 , inj₁ _otherpunct-bar-42 :: []) :: (just "P144" , nothing , just _otherpunct-bar-43 , inj₂ '(' :: []) :: []
cws-start _otherpunct-bar-42 = (just "P143" , nothing , just _otherpunct-bar-42 , inj₁ _otherpunct-bar-41 :: []) :: (just "P142" , nothing , just _otherpunct-bar-42 , inj₂ ')' :: []) :: []
cws-start _otherpunct-bar-41 = (just "P141" , nothing , just _otherpunct-bar-41 , inj₁ _otherpunct-bar-40 :: []) :: (just "P140" , nothing , just _otherpunct-bar-41 , inj₂ ':' :: []) :: []
cws-start _otherpunct-bar-40 = (just "P139" , nothing , just _otherpunct-bar-40 , inj₁ _otherpunct-bar-39 :: []) :: (just "P138" , nothing , just _otherpunct-bar-40 , inj₂ '.' :: []) :: []
cws-start _otherpunct-bar-39 = (just "P137" , nothing , just _otherpunct-bar-39 , inj₁ _otherpunct-bar-38 :: []) :: (just "P136" , nothing , just _otherpunct-bar-39 , inj₂ '[' :: []) :: []
cws-start _otherpunct-bar-38 = (just "P135" , nothing , just _otherpunct-bar-38 , inj₁ _otherpunct-bar-37 :: []) :: (just "P134" , nothing , just _otherpunct-bar-38 , inj₂ ']' :: []) :: []
cws-start _otherpunct-bar-37 = (just "P133" , nothing , just _otherpunct-bar-37 , inj₁ _otherpunct-bar-36 :: []) :: (just "P132" , nothing , just _otherpunct-bar-37 , inj₂ ',' :: []) :: []
cws-start _otherpunct-bar-36 = (just "P131" , nothing , just _otherpunct-bar-36 , inj₁ _otherpunct-bar-35 :: []) :: (just "P130" , nothing , just _otherpunct-bar-36 , inj₂ '!' :: []) :: []
cws-start _otherpunct-bar-35 = (just "P129" , nothing , just _otherpunct-bar-35 , inj₁ _otherpunct-bar-34 :: []) :: (just "P128" , nothing , just _otherpunct-bar-35 , inj₂ '{' :: []) :: []
cws-start _otherpunct-bar-34 = (just "P127" , nothing , just _otherpunct-bar-34 , inj₁ _otherpunct-bar-33 :: []) :: (just "P126" , nothing , just _otherpunct-bar-34 , inj₂ '}' :: []) :: []
cws-start _otherpunct-bar-33 = (just "P125" , nothing , just _otherpunct-bar-33 , inj₁ _otherpunct-bar-32 :: []) :: (just "P124" , nothing , just _otherpunct-bar-33 , inj₂ '⇒' :: []) :: []
cws-start _otherpunct-bar-32 = (just "P123" , nothing , just _otherpunct-bar-32 , inj₁ _otherpunct-bar-31 :: []) :: (just "P122" , nothing , just _otherpunct-bar-32 , inj₂ '?' :: []) :: []
cws-start _otherpunct-bar-31 = (just "P121" , nothing , just _otherpunct-bar-31 , inj₁ _otherpunct-bar-30 :: []) :: (just "P120" , nothing , just _otherpunct-bar-31 , inj₂ 'Λ' :: []) :: []
cws-start _otherpunct-bar-30 = (just "P119" , nothing , just _otherpunct-bar-30 , inj₁ _otherpunct-bar-29 :: []) :: (just "P118" , nothing , just _otherpunct-bar-30 , inj₂ 'ρ' :: []) :: []
cws-start _otherpunct-bar-29 = (just "P117" , nothing , just _otherpunct-bar-29 , inj₁ _otherpunct-bar-28 :: []) :: (just "P116" , nothing , just _otherpunct-bar-29 , inj₂ 'ε' :: []) :: []
cws-start _otherpunct-bar-28 = (just "P115" , nothing , just _otherpunct-bar-28 , inj₁ _otherpunct-bar-27 :: []) :: (just "P114" , nothing , just _otherpunct-bar-28 , inj₂ 'β' :: []) :: []
cws-start _otherpunct-bar-27 = (just "P113" , nothing , just _otherpunct-bar-27 , inj₁ _otherpunct-bar-26 :: []) :: (just "P112" , nothing , just _otherpunct-bar-27 , inj₂ '-' :: []) :: []
cws-start _otherpunct-bar-26 = (just "P111" , nothing , just _otherpunct-bar-26 , inj₁ _otherpunct-bar-25 :: []) :: (just "P110" , nothing , just _otherpunct-bar-26 , inj₂ '𝒌' :: []) :: []
cws-start _otherpunct-bar-25 = (just "P109" , nothing , just _otherpunct-bar-25 , inj₁ _otherpunct-bar-24 :: []) :: (just "P108" , nothing , just _otherpunct-bar-25 , inj₂ '=' :: []) :: []
cws-start _otherpunct-bar-24 = (just "P107" , nothing , just _otherpunct-bar-24 , inj₁ _otherpunct-bar-23 :: []) :: (just "P106" , nothing , just _otherpunct-bar-24 , inj₂ 'ς' :: []) :: []
cws-start _otherpunct-bar-23 = (just "P105" , nothing , just _otherpunct-bar-23 , inj₁ _otherpunct-bar-22 :: []) :: (just "P104" , nothing , just _otherpunct-bar-23 , inj₂ 'θ' :: []) :: []
cws-start _otherpunct-bar-22 = (just "P103" , nothing , just _otherpunct-bar-22 , inj₁ _otherpunct-bar-21 :: []) :: (just "P102" , nothing , just _otherpunct-bar-22 , inj₂ '+' :: []) :: []
cws-start _otherpunct-bar-21 = (just "P101" , nothing , just _otherpunct-bar-21 , inj₁ _otherpunct-bar-20 :: []) :: (just "P100" , nothing , just _otherpunct-bar-21 , inj₂ '<' :: []) :: []
cws-start _otherpunct-bar-20 = (just "P99" , nothing , just _otherpunct-bar-20 , inj₁ _otherpunct-bar-19 :: []) :: (just "P98" , nothing , just _otherpunct-bar-20 , inj₂ '>' :: []) :: []
cws-start _otherpunct-bar-19 = (just "P97" , nothing , just _otherpunct-bar-19 , inj₁ _otherpunct-bar-18 :: []) :: (just "P96" , nothing , just _otherpunct-bar-19 , inj₂ '≃' :: []) :: []
cws-start _otherpunct-bar-18 = (just "P95" , nothing , just _otherpunct-bar-18 , inj₁ _otherpunct-bar-17 :: []) :: (just "P94" , nothing , just _otherpunct-bar-18 , inj₂ '\"' :: []) :: []
cws-start _otherpunct-bar-17 = (just "P93" , nothing , just _otherpunct-bar-17 , inj₁ _otherpunct-bar-16 :: []) :: (just "P92" , nothing , just _otherpunct-bar-17 , inj₂ 'δ' :: []) :: []
cws-start _otherpunct-bar-16 = (just "P91" , nothing , just _otherpunct-bar-16 , inj₁ _otherpunct-bar-15 :: []) :: (just "P90" , nothing , just _otherpunct-bar-16 , inj₂ 'χ' :: []) :: []
cws-start _otherpunct-bar-15 = (just "P89" , nothing , just _otherpunct-bar-15 , inj₁ _otherpunct-bar-14 :: []) :: (just "P88" , nothing , just _otherpunct-bar-15 , inj₂ 'μ' :: []) :: []
cws-start _otherpunct-bar-14 = (just "P87" , nothing , just _otherpunct-bar-14 , inj₁ _otherpunct-bar-13 :: []) :: (just "P86" , nothing , just _otherpunct-bar-14 , inj₂ 'υ' :: []) :: []
cws-start _otherpunct-bar-13 = (just "P85" , nothing , just _otherpunct-bar-13 , inj₁ _otherpunct-bar-12 :: []) :: (just "P84" , nothing , just _otherpunct-bar-13 , inj₂ 'φ' :: []) :: []
cws-start _otherpunct-bar-12 = (just "P83" , nothing , just _otherpunct-bar-12 , inj₂ 'ω' :: []) :: (just "P82" , nothing , just _otherpunct-bar-12 , inj₂ '◂' :: []) :: []
cws-start _otherpunct = (just "P176" , nothing , just _otherpunct , inj₁ _otherpunct-bar-58 :: []) :: []
cws-start _numpunct-bar-9 = (just "P76" , nothing , just _numpunct-bar-9 , inj₁ _numpunct-bar-8 :: []) :: (just "P75" , nothing , just _numpunct-bar-9 , inj₂ '-' :: []) :: []
cws-start _numpunct-bar-8 = (just "P74" , nothing , just _numpunct-bar-8 , inj₁ _numpunct-bar-7 :: []) :: (just "P73" , nothing , just _numpunct-bar-8 , inj₂ '~' :: []) :: []
cws-start _numpunct-bar-7 = (just "P72" , nothing , just _numpunct-bar-7 , inj₁ _numpunct-bar-6 :: []) :: (just "P71" , nothing , just _numpunct-bar-7 , inj₂ '#' :: []) :: []
cws-start _numpunct-bar-6 = (just "P70" , nothing , just _numpunct-bar-6 , inj₂ '/' :: []) :: (just "P69" , nothing , just _numpunct-bar-6 , inj₂ '_' :: []) :: []
cws-start _numpunct-bar-11 = (just "P80" , nothing , just _numpunct-bar-11 , inj₁ _numpunct-bar-10 :: []) :: (just "P79" , nothing , just _numpunct-bar-11 , inj₁ _numone :: []) :: []
cws-start _numpunct-bar-10 = (just "P78" , nothing , just _numpunct-bar-10 , inj₁ _numpunct-bar-9 :: []) :: (just "P77" , nothing , just _numpunct-bar-10 , inj₂ '\'' :: []) :: []
cws-start _numpunct = (just "P81" , nothing , just _numpunct , inj₁ _numpunct-bar-11 :: []) :: []
cws-start _numone-range-4 = (just "P64" , nothing , just _numone-range-4 , inj₂ '9' :: []) :: (just "P63" , nothing , just _numone-range-4 , inj₂ '8' :: []) :: (just "P62" , nothing , just _numone-range-4 , inj₂ '7' :: []) :: (just "P61" , nothing , just _numone-range-4 , inj₂ '6' :: []) :: (just "P60" , nothing , just _numone-range-4 , inj₂ '5' :: []) :: (just "P59" , nothing , just _numone-range-4 , inj₂ '4' :: []) :: (just "P58" , nothing , just _numone-range-4 , inj₂ '3' :: []) :: (just "P57" , nothing , just _numone-range-4 , inj₂ '2' :: []) :: (just "P56" , nothing , just _numone-range-4 , inj₂ '1' :: []) :: (just "P55" , nothing , just _numone-range-4 , inj₂ '0' :: []) :: []
cws-start _numone = (just "P65" , nothing , just _numone , inj₁ _numone-range-4 :: []) :: []
cws-start _num-plus-5 = (just "P67" , nothing , just _num-plus-5 , inj₁ _numone :: inj₁ _num-plus-5 :: []) :: (just "P66" , nothing , just _num-plus-5 , inj₁ _numone :: []) :: []
cws-start _num = (just "P68" , nothing , just _num , inj₁ _num-plus-5 :: []) :: []
cws-start _nonws-plus-70 = (just "P205" , nothing , just _nonws-plus-70 , inj₁ _anynonwschar :: inj₁ _nonws-plus-70 :: []) :: (just "P204" , nothing , just _nonws-plus-70 , inj₁ _anynonwschar :: []) :: []
cws-start _nonws = (just "P206" , nothing , just _nonws , inj₁ _nonws-plus-70 :: []) :: []
cws-start _entity = (just "EntityWs" , nothing , just _entity , inj₁ _posinfo :: inj₁ _ws :: inj₁ _posinfo :: []) :: (just "EntityNonws" , nothing , just _entity , inj₁ _nonws :: []) :: (just "EntityComment" , nothing , just _entity , inj₁ _posinfo :: inj₁ _comment :: inj₁ _posinfo :: []) :: []
cws-start _entities = (just "Entity" , nothing , just _entities , inj₁ _entity :: inj₁ _entities :: []) :: (just "EndEntity" , nothing , just _entities , []) :: []
cws-start _comment-star-64 = (just "P189" , nothing , just _comment-star-64 , inj₁ _anychar :: inj₁ _comment-star-64 :: []) :: (just "P188" , nothing , just _comment-star-64 , []) :: []
cws-start _comment = (just "P190" , nothing , just _comment , inj₂ '%' :: inj₁ _comment-star-64 :: inj₂ '\n' :: []) :: []
cws-start _aws-bar-66 = (just "P194" , nothing , just _aws-bar-66 , inj₁ _aws-bar-65 :: []) :: (just "P193" , nothing , just _aws-bar-66 , inj₂ '\n' :: []) :: []
cws-start _aws-bar-65 = (just "P192" , nothing , just _aws-bar-65 , inj₂ ' ' :: []) :: (just "P191" , nothing , just _aws-bar-65 , inj₂ '\t' :: []) :: []
cws-start _aws = (just "P195" , nothing , just _aws , inj₁ _aws-bar-66 :: []) :: []
cws-start _anynonwschar-bar-69 = (just "P202" , nothing , just _anynonwschar-bar-69 , inj₁ _anynonwschar-bar-68 :: []) :: (just "P201" , nothing , just _anynonwschar-bar-69 , inj₁ _alpha :: []) :: []
cws-start _anynonwschar-bar-68 = (just "P200" , nothing , just _anynonwschar-bar-68 , inj₁ _otherpunct :: []) :: (just "P199" , nothing , just _anynonwschar-bar-68 , inj₁ _numpunct :: []) :: []
cws-start _anynonwschar = (just "P203" , nothing , just _anynonwschar , inj₁ _anynonwschar-bar-69 :: []) :: []
cws-start _anychar-bar-63 = (just "P186" , nothing , just _anychar-bar-63 , inj₁ _anychar-bar-62 :: []) :: (just "P185" , nothing , just _anychar-bar-63 , inj₁ _alpha :: []) :: []
cws-start _anychar-bar-62 = (just "P184" , nothing , just _anychar-bar-62 , inj₁ _anychar-bar-61 :: []) :: (just "P183" , nothing , just _anychar-bar-62 , inj₁ _numpunct :: []) :: []
cws-start _anychar-bar-61 = (just "P182" , nothing , just _anychar-bar-61 , inj₁ _anychar-bar-60 :: []) :: (just "P181" , nothing , just _anychar-bar-61 , inj₂ '\t' :: []) :: []
cws-start _anychar-bar-60 = (just "P180" , nothing , just _anychar-bar-60 , inj₁ _anychar-bar-59 :: []) :: (just "P179" , nothing , just _anychar-bar-60 , inj₂ ' ' :: []) :: []
cws-start _anychar-bar-59 = (just "P178" , nothing , just _anychar-bar-59 , inj₁ _otherpunct :: []) :: (just "P177" , nothing , just _anychar-bar-59 , inj₂ '%' :: []) :: []
cws-start _anychar = (just "P187" , nothing , just _anychar , inj₁ _anychar-bar-63 :: []) :: []
cws-start _alpha-range-2 = (just "P51" , nothing , just _alpha-range-2 , inj₂ 'Z' :: []) :: (just "P50" , nothing , just _alpha-range-2 , inj₂ 'Y' :: []) :: (just "P49" , nothing , just _alpha-range-2 , inj₂ 'X' :: []) :: (just "P48" , nothing , just _alpha-range-2 , inj₂ 'W' :: []) :: (just "P47" , nothing , just _alpha-range-2 , inj₂ 'V' :: []) :: (just "P46" , nothing , just _alpha-range-2 , inj₂ 'U' :: []) :: (just "P45" , nothing , just _alpha-range-2 , inj₂ 'T' :: []) :: (just "P44" , nothing , just _alpha-range-2 , inj₂ 'S' :: []) :: (just "P43" , nothing , just _alpha-range-2 , inj₂ 'R' :: []) :: (just "P42" , nothing , just _alpha-range-2 , inj₂ 'Q' :: []) :: (just "P41" , nothing , just _alpha-range-2 , inj₂ 'P' :: []) :: (just "P40" , nothing , just _alpha-range-2 , inj₂ 'O' :: []) :: (just "P39" , nothing , just _alpha-range-2 , inj₂ 'N' :: []) :: (just "P38" , nothing , just _alpha-range-2 , inj₂ 'M' :: []) :: (just "P37" , nothing , just _alpha-range-2 , inj₂ 'L' :: []) :: (just "P36" , nothing , just _alpha-range-2 , inj₂ 'K' :: []) :: (just "P35" , nothing , just _alpha-range-2 , inj₂ 'J' :: []) :: (just "P34" , nothing , just _alpha-range-2 , inj₂ 'I' :: []) :: (just "P33" , nothing , just _alpha-range-2 , inj₂ 'H' :: []) :: (just "P32" , nothing , just _alpha-range-2 , inj₂ 'G' :: []) :: (just "P31" , nothing , just _alpha-range-2 , inj₂ 'F' :: []) :: (just "P30" , nothing , just _alpha-range-2 , inj₂ 'E' :: []) :: (just "P29" , nothing , just _alpha-range-2 , inj₂ 'D' :: []) :: (just "P28" , nothing , just _alpha-range-2 , inj₂ 'C' :: []) :: (just "P27" , nothing , just _alpha-range-2 , inj₂ 'B' :: []) :: (just "P26" , nothing , just _alpha-range-2 , inj₂ 'A' :: []) :: []
cws-start _alpha-range-1 = (just "P9" , nothing , just _alpha-range-1 , inj₂ 'j' :: []) :: (just "P8" , nothing , just _alpha-range-1 , inj₂ 'i' :: []) :: (just "P7" , nothing , just _alpha-range-1 , inj₂ 'h' :: []) :: (just "P6" , nothing , just _alpha-range-1 , inj₂ 'g' :: []) :: (just "P5" , nothing , just _alpha-range-1 , inj₂ 'f' :: []) :: (just "P4" , nothing , just _alpha-range-1 , inj₂ 'e' :: []) :: (just "P3" , nothing , just _alpha-range-1 , inj₂ 'd' :: []) :: (just "P25" , nothing , just _alpha-range-1 , inj₂ 'z' :: []) :: (just "P24" , nothing , just _alpha-range-1 , inj₂ 'y' :: []) :: (just "P23" , nothing , just _alpha-range-1 , inj₂ 'x' :: []) :: (just "P22" , nothing , just _alpha-range-1 , inj₂ 'w' :: []) :: (just "P21" , nothing , just _alpha-range-1 , inj₂ 'v' :: []) :: (just "P20" , nothing , just _alpha-range-1 , inj₂ 'u' :: []) :: (just "P2" , nothing , just _alpha-range-1 , inj₂ 'c' :: []) :: (just "P19" , nothing , just _alpha-range-1 , inj₂ 't' :: []) :: (just "P18" , nothing , just _alpha-range-1 , inj₂ 's' :: []) :: (just "P17" , nothing , just _alpha-range-1 , inj₂ 'r' :: []) :: (just "P16" , nothing , just _alpha-range-1 , inj₂ 'q' :: []) :: (just "P15" , nothing , just _alpha-range-1 , inj₂ 'p' :: []) :: (just "P14" , nothing , just _alpha-range-1 , inj₂ 'o' :: []) :: (just "P13" , nothing , just _alpha-range-1 , inj₂ 'n' :: []) :: (just "P12" , nothing , just _alpha-range-1 , inj₂ 'm' :: []) :: (just "P11" , nothing , just _alpha-range-1 , inj₂ 'l' :: []) :: (just "P10" , nothing , just _alpha-range-1 , inj₂ 'k' :: []) :: (just "P1" , nothing , just _alpha-range-1 , inj₂ 'b' :: []) :: (just "P0" , nothing , just _alpha-range-1 , inj₂ 'a' :: []) :: []
cws-start _alpha-bar-3 = (just "P53" , nothing , just _alpha-bar-3 , inj₁ _alpha-range-2 :: []) :: (just "P52" , nothing , just _alpha-bar-3 , inj₁ _alpha-range-1 :: []) :: []
cws-start _alpha = (just "P54" , nothing , just _alpha , inj₁ _alpha-bar-3 :: []) :: []


cws-return : maybe gratr2-nt → 𝕃 gratr2-rule
cws-return _ = []

cws-rtn : gratr2-rtn
cws-rtn = record { start = _start ; _eq_ = gratr2-nt-eq ; gratr2-start = cws-start ; gratr2-return = cws-return }

open import run ptr
open noderiv

------------------------------------------
-- Length-decreasing rules
------------------------------------------

len-dec-rewrite : Run → maybe (Run × ℕ)
len-dec-rewrite {- Entity-} ((Id "Entity") :: (ParseTree (parsed-entity x0)) :: _::_(ParseTree (parsed-entities x1)) rest) = just (ParseTree (parsed-entities (norm-entities (Entity x0 x1))) ::' rest , 3)
len-dec-rewrite {- EntityComment-} ((Id "EntityComment") :: (ParseTree (parsed-posinfo x0)) :: (ParseTree parsed-comment) :: _::_(ParseTree (parsed-posinfo x1)) rest) = just (ParseTree (parsed-entity (norm-entity (EntityComment x0 x1))) ::' rest , 4)
len-dec-rewrite {- EntityNonws-} ((Id "EntityNonws") :: _::_(ParseTree parsed-nonws) rest) = just (ParseTree (parsed-entity (norm-entity EntityNonws)) ::' rest , 2)
len-dec-rewrite {- EntityWs-} ((Id "EntityWs") :: (ParseTree (parsed-posinfo x0)) :: (ParseTree parsed-ws) :: _::_(ParseTree (parsed-posinfo x1)) rest) = just (ParseTree (parsed-entity (norm-entity (EntityWs x0 x1))) ::' rest , 4)
len-dec-rewrite {- File-} ((Id "File") :: _::_(ParseTree (parsed-entities x0)) rest) = just (ParseTree (parsed-start (norm-start (File x0))) ::' rest , 2)
len-dec-rewrite {- P0-} ((Id "P0") :: _::_(InputChar 'a') rest) = just (ParseTree parsed-alpha-range-1 ::' rest , 2)
len-dec-rewrite {- P1-} ((Id "P1") :: _::_(InputChar 'b') rest) = just (ParseTree parsed-alpha-range-1 ::' rest , 2)
len-dec-rewrite {- P10-} ((Id "P10") :: _::_(InputChar 'k') rest) = just (ParseTree parsed-alpha-range-1 ::' rest , 2)
len-dec-rewrite {- P100-} ((Id "P100") :: _::_(InputChar '<') rest) = just (ParseTree parsed-otherpunct-bar-21 ::' rest , 2)
len-dec-rewrite {- P101-} ((Id "P101") :: _::_(ParseTree parsed-otherpunct-bar-20) rest) = just (ParseTree parsed-otherpunct-bar-21 ::' rest , 2)
len-dec-rewrite {- P102-} ((Id "P102") :: _::_(InputChar '+') rest) = just (ParseTree parsed-otherpunct-bar-22 ::' rest , 2)
len-dec-rewrite {- P103-} ((Id "P103") :: _::_(ParseTree parsed-otherpunct-bar-21) rest) = just (ParseTree parsed-otherpunct-bar-22 ::' rest , 2)
len-dec-rewrite {- P104-} ((Id "P104") :: _::_(InputChar 'θ') rest) = just (ParseTree parsed-otherpunct-bar-23 ::' rest , 2)
len-dec-rewrite {- P105-} ((Id "P105") :: _::_(ParseTree parsed-otherpunct-bar-22) rest) = just (ParseTree parsed-otherpunct-bar-23 ::' rest , 2)
len-dec-rewrite {- P106-} ((Id "P106") :: _::_(InputChar 'ς') rest) = just (ParseTree parsed-otherpunct-bar-24 ::' rest , 2)
len-dec-rewrite {- P107-} ((Id "P107") :: _::_(ParseTree parsed-otherpunct-bar-23) rest) = just (ParseTree parsed-otherpunct-bar-24 ::' rest , 2)
len-dec-rewrite {- P108-} ((Id "P108") :: _::_(InputChar '=') rest) = just (ParseTree parsed-otherpunct-bar-25 ::' rest , 2)
len-dec-rewrite {- P109-} ((Id "P109") :: _::_(ParseTree parsed-otherpunct-bar-24) rest) = just (ParseTree parsed-otherpunct-bar-25 ::' rest , 2)
len-dec-rewrite {- P11-} ((Id "P11") :: _::_(InputChar 'l') rest) = just (ParseTree parsed-alpha-range-1 ::' rest , 2)
len-dec-rewrite {- P110-} ((Id "P110") :: _::_(InputChar '𝒌') rest) = just (ParseTree parsed-otherpunct-bar-26 ::' rest , 2)
len-dec-rewrite {- P111-} ((Id "P111") :: _::_(ParseTree parsed-otherpunct-bar-25) rest) = just (ParseTree parsed-otherpunct-bar-26 ::' rest , 2)
len-dec-rewrite {- P112-} ((Id "P112") :: _::_(InputChar '-') rest) = just (ParseTree parsed-otherpunct-bar-27 ::' rest , 2)
len-dec-rewrite {- P113-} ((Id "P113") :: _::_(ParseTree parsed-otherpunct-bar-26) rest) = just (ParseTree parsed-otherpunct-bar-27 ::' rest , 2)
len-dec-rewrite {- P114-} ((Id "P114") :: _::_(InputChar 'β') rest) = just (ParseTree parsed-otherpunct-bar-28 ::' rest , 2)
len-dec-rewrite {- P115-} ((Id "P115") :: _::_(ParseTree parsed-otherpunct-bar-27) rest) = just (ParseTree parsed-otherpunct-bar-28 ::' rest , 2)
len-dec-rewrite {- P116-} ((Id "P116") :: _::_(InputChar 'ε') rest) = just (ParseTree parsed-otherpunct-bar-29 ::' rest , 2)
len-dec-rewrite {- P117-} ((Id "P117") :: _::_(ParseTree parsed-otherpunct-bar-28) rest) = just (ParseTree parsed-otherpunct-bar-29 ::' rest , 2)
len-dec-rewrite {- P118-} ((Id "P118") :: _::_(InputChar 'ρ') rest) = just (ParseTree parsed-otherpunct-bar-30 ::' rest , 2)
len-dec-rewrite {- P119-} ((Id "P119") :: _::_(ParseTree parsed-otherpunct-bar-29) rest) = just (ParseTree parsed-otherpunct-bar-30 ::' rest , 2)
len-dec-rewrite {- P12-} ((Id "P12") :: _::_(InputChar 'm') rest) = just (ParseTree parsed-alpha-range-1 ::' rest , 2)
len-dec-rewrite {- P120-} ((Id "P120") :: _::_(InputChar 'Λ') rest) = just (ParseTree parsed-otherpunct-bar-31 ::' rest , 2)
len-dec-rewrite {- P121-} ((Id "P121") :: _::_(ParseTree parsed-otherpunct-bar-30) rest) = just (ParseTree parsed-otherpunct-bar-31 ::' rest , 2)
len-dec-rewrite {- P122-} ((Id "P122") :: _::_(InputChar '?') rest) = just (ParseTree parsed-otherpunct-bar-32 ::' rest , 2)
len-dec-rewrite {- P123-} ((Id "P123") :: _::_(ParseTree parsed-otherpunct-bar-31) rest) = just (ParseTree parsed-otherpunct-bar-32 ::' rest , 2)
len-dec-rewrite {- P124-} ((Id "P124") :: _::_(InputChar '⇒') rest) = just (ParseTree parsed-otherpunct-bar-33 ::' rest , 2)
len-dec-rewrite {- P125-} ((Id "P125") :: _::_(ParseTree parsed-otherpunct-bar-32) rest) = just (ParseTree parsed-otherpunct-bar-33 ::' rest , 2)
len-dec-rewrite {- P126-} ((Id "P126") :: _::_(InputChar '}') rest) = just (ParseTree parsed-otherpunct-bar-34 ::' rest , 2)
len-dec-rewrite {- P127-} ((Id "P127") :: _::_(ParseTree parsed-otherpunct-bar-33) rest) = just (ParseTree parsed-otherpunct-bar-34 ::' rest , 2)
len-dec-rewrite {- P128-} ((Id "P128") :: _::_(InputChar '{') rest) = just (ParseTree parsed-otherpunct-bar-35 ::' rest , 2)
len-dec-rewrite {- P129-} ((Id "P129") :: _::_(ParseTree parsed-otherpunct-bar-34) rest) = just (ParseTree parsed-otherpunct-bar-35 ::' rest , 2)
len-dec-rewrite {- P13-} ((Id "P13") :: _::_(InputChar 'n') rest) = just (ParseTree parsed-alpha-range-1 ::' rest , 2)
len-dec-rewrite {- P130-} ((Id "P130") :: _::_(InputChar '!') rest) = just (ParseTree parsed-otherpunct-bar-36 ::' rest , 2)
len-dec-rewrite {- P131-} ((Id "P131") :: _::_(ParseTree parsed-otherpunct-bar-35) rest) = just (ParseTree parsed-otherpunct-bar-36 ::' rest , 2)
len-dec-rewrite {- P132-} ((Id "P132") :: _::_(InputChar ',') rest) = just (ParseTree parsed-otherpunct-bar-37 ::' rest , 2)
len-dec-rewrite {- P133-} ((Id "P133") :: _::_(ParseTree parsed-otherpunct-bar-36) rest) = just (ParseTree parsed-otherpunct-bar-37 ::' rest , 2)
len-dec-rewrite {- P134-} ((Id "P134") :: _::_(InputChar ']') rest) = just (ParseTree parsed-otherpunct-bar-38 ::' rest , 2)
len-dec-rewrite {- P135-} ((Id "P135") :: _::_(ParseTree parsed-otherpunct-bar-37) rest) = just (ParseTree parsed-otherpunct-bar-38 ::' rest , 2)
len-dec-rewrite {- P136-} ((Id "P136") :: _::_(InputChar '[') rest) = just (ParseTree parsed-otherpunct-bar-39 ::' rest , 2)
len-dec-rewrite {- P137-} ((Id "P137") :: _::_(ParseTree parsed-otherpunct-bar-38) rest) = just (ParseTree parsed-otherpunct-bar-39 ::' rest , 2)
len-dec-rewrite {- P138-} ((Id "P138") :: _::_(InputChar '.') rest) = just (ParseTree parsed-otherpunct-bar-40 ::' rest , 2)
len-dec-rewrite {- P139-} ((Id "P139") :: _::_(ParseTree parsed-otherpunct-bar-39) rest) = just (ParseTree parsed-otherpunct-bar-40 ::' rest , 2)
len-dec-rewrite {- P14-} ((Id "P14") :: _::_(InputChar 'o') rest) = just (ParseTree parsed-alpha-range-1 ::' rest , 2)
len-dec-rewrite {- P140-} ((Id "P140") :: _::_(InputChar ':') rest) = just (ParseTree parsed-otherpunct-bar-41 ::' rest , 2)
len-dec-rewrite {- P141-} ((Id "P141") :: _::_(ParseTree parsed-otherpunct-bar-40) rest) = just (ParseTree parsed-otherpunct-bar-41 ::' rest , 2)
len-dec-rewrite {- P142-} ((Id "P142") :: _::_(InputChar ')') rest) = just (ParseTree parsed-otherpunct-bar-42 ::' rest , 2)
len-dec-rewrite {- P143-} ((Id "P143") :: _::_(ParseTree parsed-otherpunct-bar-41) rest) = just (ParseTree parsed-otherpunct-bar-42 ::' rest , 2)
len-dec-rewrite {- P144-} ((Id "P144") :: _::_(InputChar '(') rest) = just (ParseTree parsed-otherpunct-bar-43 ::' rest , 2)
len-dec-rewrite {- P145-} ((Id "P145") :: _::_(ParseTree parsed-otherpunct-bar-42) rest) = just (ParseTree parsed-otherpunct-bar-43 ::' rest , 2)
len-dec-rewrite {- P146-} ((Id "P146") :: _::_(InputChar '●') rest) = just (ParseTree parsed-otherpunct-bar-44 ::' rest , 2)
len-dec-rewrite {- P147-} ((Id "P147") :: _::_(ParseTree parsed-otherpunct-bar-43) rest) = just (ParseTree parsed-otherpunct-bar-44 ::' rest , 2)
len-dec-rewrite {- P148-} ((Id "P148") :: _::_(InputChar '↑') rest) = just (ParseTree parsed-otherpunct-bar-45 ::' rest , 2)
len-dec-rewrite {- P149-} ((Id "P149") :: _::_(ParseTree parsed-otherpunct-bar-44) rest) = just (ParseTree parsed-otherpunct-bar-45 ::' rest , 2)
len-dec-rewrite {- P15-} ((Id "P15") :: _::_(InputChar 'p') rest) = just (ParseTree parsed-alpha-range-1 ::' rest , 2)
len-dec-rewrite {- P150-} ((Id "P150") :: _::_(InputChar '➾') rest) = just (ParseTree parsed-otherpunct-bar-46 ::' rest , 2)
len-dec-rewrite {- P151-} ((Id "P151") :: _::_(ParseTree parsed-otherpunct-bar-45) rest) = just (ParseTree parsed-otherpunct-bar-46 ::' rest , 2)
len-dec-rewrite {- P152-} ((Id "P152") :: _::_(InputChar '➔') rest) = just (ParseTree parsed-otherpunct-bar-47 ::' rest , 2)
len-dec-rewrite {- P153-} ((Id "P153") :: _::_(ParseTree parsed-otherpunct-bar-46) rest) = just (ParseTree parsed-otherpunct-bar-47 ::' rest , 2)
len-dec-rewrite {- P154-} ((Id "P154") :: _::_(InputChar '⇐') rest) = just (ParseTree parsed-otherpunct-bar-48 ::' rest , 2)
len-dec-rewrite {- P155-} ((Id "P155") :: _::_(ParseTree parsed-otherpunct-bar-47) rest) = just (ParseTree parsed-otherpunct-bar-48 ::' rest , 2)
len-dec-rewrite {- P156-} ((Id "P156") :: _::_(InputChar '·') rest) = just (ParseTree parsed-otherpunct-bar-49 ::' rest , 2)
len-dec-rewrite {- P157-} ((Id "P157") :: _::_(ParseTree parsed-otherpunct-bar-48) rest) = just (ParseTree parsed-otherpunct-bar-49 ::' rest , 2)
len-dec-rewrite {- P158-} ((Id "P158") :: _::_(InputChar '☆') rest) = just (ParseTree parsed-otherpunct-bar-50 ::' rest , 2)
len-dec-rewrite {- P159-} ((Id "P159") :: _::_(ParseTree parsed-otherpunct-bar-49) rest) = just (ParseTree parsed-otherpunct-bar-50 ::' rest , 2)
len-dec-rewrite {- P16-} ((Id "P16") :: _::_(InputChar 'q') rest) = just (ParseTree parsed-alpha-range-1 ::' rest , 2)
len-dec-rewrite {- P160-} ((Id "P160") :: _::_(InputChar '★') rest) = just (ParseTree parsed-otherpunct-bar-51 ::' rest , 2)
len-dec-rewrite {- P161-} ((Id "P161") :: _::_(ParseTree parsed-otherpunct-bar-50) rest) = just (ParseTree parsed-otherpunct-bar-51 ::' rest , 2)
len-dec-rewrite {- P162-} ((Id "P162") :: _::_(InputChar 'π') rest) = just (ParseTree parsed-otherpunct-bar-52 ::' rest , 2)
len-dec-rewrite {- P163-} ((Id "P163") :: _::_(ParseTree parsed-otherpunct-bar-51) rest) = just (ParseTree parsed-otherpunct-bar-52 ::' rest , 2)
len-dec-rewrite {- P164-} ((Id "P164") :: _::_(InputChar '∀') rest) = just (ParseTree parsed-otherpunct-bar-53 ::' rest , 2)
len-dec-rewrite {- P165-} ((Id "P165") :: _::_(ParseTree parsed-otherpunct-bar-52) rest) = just (ParseTree parsed-otherpunct-bar-53 ::' rest , 2)
len-dec-rewrite {- P166-} ((Id "P166") :: _::_(InputChar 'λ') rest) = just (ParseTree parsed-otherpunct-bar-54 ::' rest , 2)
len-dec-rewrite {- P167-} ((Id "P167") :: _::_(ParseTree parsed-otherpunct-bar-53) rest) = just (ParseTree parsed-otherpunct-bar-54 ::' rest , 2)
len-dec-rewrite {- P168-} ((Id "P168") :: _::_(InputChar 'ι') rest) = just (ParseTree parsed-otherpunct-bar-55 ::' rest , 2)
len-dec-rewrite {- P169-} ((Id "P169") :: _::_(ParseTree parsed-otherpunct-bar-54) rest) = just (ParseTree parsed-otherpunct-bar-55 ::' rest , 2)
len-dec-rewrite {- P17-} ((Id "P17") :: _::_(InputChar 'r') rest) = just (ParseTree parsed-alpha-range-1 ::' rest , 2)
len-dec-rewrite {- P170-} ((Id "P170") :: _::_(InputChar 'Π') rest) = just (ParseTree parsed-otherpunct-bar-56 ::' rest , 2)
len-dec-rewrite {- P171-} ((Id "P171") :: _::_(ParseTree parsed-otherpunct-bar-55) rest) = just (ParseTree parsed-otherpunct-bar-56 ::' rest , 2)
len-dec-rewrite {- P172-} ((Id "P172") :: _::_(InputChar '□') rest) = just (ParseTree parsed-otherpunct-bar-57 ::' rest , 2)
len-dec-rewrite {- P173-} ((Id "P173") :: _::_(ParseTree parsed-otherpunct-bar-56) rest) = just (ParseTree parsed-otherpunct-bar-57 ::' rest , 2)
len-dec-rewrite {- P174-} ((Id "P174") :: _::_(InputChar '|') rest) = just (ParseTree parsed-otherpunct-bar-58 ::' rest , 2)
len-dec-rewrite {- P175-} ((Id "P175") :: _::_(ParseTree parsed-otherpunct-bar-57) rest) = just (ParseTree parsed-otherpunct-bar-58 ::' rest , 2)
len-dec-rewrite {- P176-} ((Id "P176") :: _::_(ParseTree parsed-otherpunct-bar-58) rest) = just (ParseTree parsed-otherpunct ::' rest , 2)
len-dec-rewrite {- P177-} ((Id "P177") :: _::_(InputChar '%') rest) = just (ParseTree parsed-anychar-bar-59 ::' rest , 2)
len-dec-rewrite {- P178-} ((Id "P178") :: _::_(ParseTree parsed-otherpunct) rest) = just (ParseTree parsed-anychar-bar-59 ::' rest , 2)
len-dec-rewrite {- P179-} ((Id "P179") :: _::_(InputChar ' ') rest) = just (ParseTree parsed-anychar-bar-60 ::' rest , 2)
len-dec-rewrite {- P18-} ((Id "P18") :: _::_(InputChar 's') rest) = just (ParseTree parsed-alpha-range-1 ::' rest , 2)
len-dec-rewrite {- P180-} ((Id "P180") :: _::_(ParseTree parsed-anychar-bar-59) rest) = just (ParseTree parsed-anychar-bar-60 ::' rest , 2)
len-dec-rewrite {- P181-} ((Id "P181") :: _::_(InputChar '\t') rest) = just (ParseTree parsed-anychar-bar-61 ::' rest , 2)
len-dec-rewrite {- P182-} ((Id "P182") :: _::_(ParseTree parsed-anychar-bar-60) rest) = just (ParseTree parsed-anychar-bar-61 ::' rest , 2)
len-dec-rewrite {- P183-} ((Id "P183") :: _::_(ParseTree parsed-numpunct) rest) = just (ParseTree parsed-anychar-bar-62 ::' rest , 2)
len-dec-rewrite {- P184-} ((Id "P184") :: _::_(ParseTree parsed-anychar-bar-61) rest) = just (ParseTree parsed-anychar-bar-62 ::' rest , 2)
len-dec-rewrite {- P185-} ((Id "P185") :: _::_(ParseTree parsed-alpha) rest) = just (ParseTree parsed-anychar-bar-63 ::' rest , 2)
len-dec-rewrite {- P186-} ((Id "P186") :: _::_(ParseTree parsed-anychar-bar-62) rest) = just (ParseTree parsed-anychar-bar-63 ::' rest , 2)
len-dec-rewrite {- P187-} ((Id "P187") :: _::_(ParseTree parsed-anychar-bar-63) rest) = just (ParseTree parsed-anychar ::' rest , 2)
len-dec-rewrite {- P189-} ((Id "P189") :: (ParseTree parsed-anychar) :: _::_(ParseTree parsed-comment-star-64) rest) = just (ParseTree parsed-comment-star-64 ::' rest , 3)
len-dec-rewrite {- P19-} ((Id "P19") :: _::_(InputChar 't') rest) = just (ParseTree parsed-alpha-range-1 ::' rest , 2)
len-dec-rewrite {- P190-} ((Id "P190") :: (InputChar '%') :: (ParseTree parsed-comment-star-64) :: _::_(InputChar '\n') rest) = just (ParseTree parsed-comment ::' rest , 4)
len-dec-rewrite {- P191-} ((Id "P191") :: _::_(InputChar '\t') rest) = just (ParseTree parsed-aws-bar-65 ::' rest , 2)
len-dec-rewrite {- P192-} ((Id "P192") :: _::_(InputChar ' ') rest) = just (ParseTree parsed-aws-bar-65 ::' rest , 2)
len-dec-rewrite {- P193-} ((Id "P193") :: _::_(InputChar '\n') rest) = just (ParseTree parsed-aws-bar-66 ::' rest , 2)
len-dec-rewrite {- P194-} ((Id "P194") :: _::_(ParseTree parsed-aws-bar-65) rest) = just (ParseTree parsed-aws-bar-66 ::' rest , 2)
len-dec-rewrite {- P195-} ((Id "P195") :: _::_(ParseTree parsed-aws-bar-66) rest) = just (ParseTree parsed-aws ::' rest , 2)
len-dec-rewrite {- P196-} ((Id "P196") :: _::_(ParseTree parsed-aws) rest) = just (ParseTree parsed-ws-plus-67 ::' rest , 2)
len-dec-rewrite {- P197-} ((Id "P197") :: (ParseTree parsed-aws) :: _::_(ParseTree parsed-ws-plus-67) rest) = just (ParseTree parsed-ws-plus-67 ::' rest , 3)
len-dec-rewrite {- P198-} ((Id "P198") :: _::_(ParseTree parsed-ws-plus-67) rest) = just (ParseTree parsed-ws ::' rest , 2)
len-dec-rewrite {- P199-} ((Id "P199") :: _::_(ParseTree parsed-numpunct) rest) = just (ParseTree parsed-anynonwschar-bar-68 ::' rest , 2)
len-dec-rewrite {- P2-} ((Id "P2") :: _::_(InputChar 'c') rest) = just (ParseTree parsed-alpha-range-1 ::' rest , 2)
len-dec-rewrite {- P20-} ((Id "P20") :: _::_(InputChar 'u') rest) = just (ParseTree parsed-alpha-range-1 ::' rest , 2)
len-dec-rewrite {- P200-} ((Id "P200") :: _::_(ParseTree parsed-otherpunct) rest) = just (ParseTree parsed-anynonwschar-bar-68 ::' rest , 2)
len-dec-rewrite {- P201-} ((Id "P201") :: _::_(ParseTree parsed-alpha) rest) = just (ParseTree parsed-anynonwschar-bar-69 ::' rest , 2)
len-dec-rewrite {- P202-} ((Id "P202") :: _::_(ParseTree parsed-anynonwschar-bar-68) rest) = just (ParseTree parsed-anynonwschar-bar-69 ::' rest , 2)
len-dec-rewrite {- P203-} ((Id "P203") :: _::_(ParseTree parsed-anynonwschar-bar-69) rest) = just (ParseTree parsed-anynonwschar ::' rest , 2)
len-dec-rewrite {- P204-} ((Id "P204") :: _::_(ParseTree parsed-anynonwschar) rest) = just (ParseTree parsed-nonws-plus-70 ::' rest , 2)
len-dec-rewrite {- P205-} ((Id "P205") :: (ParseTree parsed-anynonwschar) :: _::_(ParseTree parsed-nonws-plus-70) rest) = just (ParseTree parsed-nonws-plus-70 ::' rest , 3)
len-dec-rewrite {- P206-} ((Id "P206") :: _::_(ParseTree parsed-nonws-plus-70) rest) = just (ParseTree parsed-nonws ::' rest , 2)
len-dec-rewrite {- P21-} ((Id "P21") :: _::_(InputChar 'v') rest) = just (ParseTree parsed-alpha-range-1 ::' rest , 2)
len-dec-rewrite {- P22-} ((Id "P22") :: _::_(InputChar 'w') rest) = just (ParseTree parsed-alpha-range-1 ::' rest , 2)
len-dec-rewrite {- P23-} ((Id "P23") :: _::_(InputChar 'x') rest) = just (ParseTree parsed-alpha-range-1 ::' rest , 2)
len-dec-rewrite {- P24-} ((Id "P24") :: _::_(InputChar 'y') rest) = just (ParseTree parsed-alpha-range-1 ::' rest , 2)
len-dec-rewrite {- P25-} ((Id "P25") :: _::_(InputChar 'z') rest) = just (ParseTree parsed-alpha-range-1 ::' rest , 2)
len-dec-rewrite {- P26-} ((Id "P26") :: _::_(InputChar 'A') rest) = just (ParseTree parsed-alpha-range-2 ::' rest , 2)
len-dec-rewrite {- P27-} ((Id "P27") :: _::_(InputChar 'B') rest) = just (ParseTree parsed-alpha-range-2 ::' rest , 2)
len-dec-rewrite {- P28-} ((Id "P28") :: _::_(InputChar 'C') rest) = just (ParseTree parsed-alpha-range-2 ::' rest , 2)
len-dec-rewrite {- P29-} ((Id "P29") :: _::_(InputChar 'D') rest) = just (ParseTree parsed-alpha-range-2 ::' rest , 2)
len-dec-rewrite {- P3-} ((Id "P3") :: _::_(InputChar 'd') rest) = just (ParseTree parsed-alpha-range-1 ::' rest , 2)
len-dec-rewrite {- P30-} ((Id "P30") :: _::_(InputChar 'E') rest) = just (ParseTree parsed-alpha-range-2 ::' rest , 2)
len-dec-rewrite {- P31-} ((Id "P31") :: _::_(InputChar 'F') rest) = just (ParseTree parsed-alpha-range-2 ::' rest , 2)
len-dec-rewrite {- P32-} ((Id "P32") :: _::_(InputChar 'G') rest) = just (ParseTree parsed-alpha-range-2 ::' rest , 2)
len-dec-rewrite {- P33-} ((Id "P33") :: _::_(InputChar 'H') rest) = just (ParseTree parsed-alpha-range-2 ::' rest , 2)
len-dec-rewrite {- P34-} ((Id "P34") :: _::_(InputChar 'I') rest) = just (ParseTree parsed-alpha-range-2 ::' rest , 2)
len-dec-rewrite {- P35-} ((Id "P35") :: _::_(InputChar 'J') rest) = just (ParseTree parsed-alpha-range-2 ::' rest , 2)
len-dec-rewrite {- P36-} ((Id "P36") :: _::_(InputChar 'K') rest) = just (ParseTree parsed-alpha-range-2 ::' rest , 2)
len-dec-rewrite {- P37-} ((Id "P37") :: _::_(InputChar 'L') rest) = just (ParseTree parsed-alpha-range-2 ::' rest , 2)
len-dec-rewrite {- P38-} ((Id "P38") :: _::_(InputChar 'M') rest) = just (ParseTree parsed-alpha-range-2 ::' rest , 2)
len-dec-rewrite {- P39-} ((Id "P39") :: _::_(InputChar 'N') rest) = just (ParseTree parsed-alpha-range-2 ::' rest , 2)
len-dec-rewrite {- P4-} ((Id "P4") :: _::_(InputChar 'e') rest) = just (ParseTree parsed-alpha-range-1 ::' rest , 2)
len-dec-rewrite {- P40-} ((Id "P40") :: _::_(InputChar 'O') rest) = just (ParseTree parsed-alpha-range-2 ::' rest , 2)
len-dec-rewrite {- P41-} ((Id "P41") :: _::_(InputChar 'P') rest) = just (ParseTree parsed-alpha-range-2 ::' rest , 2)
len-dec-rewrite {- P42-} ((Id "P42") :: _::_(InputChar 'Q') rest) = just (ParseTree parsed-alpha-range-2 ::' rest , 2)
len-dec-rewrite {- P43-} ((Id "P43") :: _::_(InputChar 'R') rest) = just (ParseTree parsed-alpha-range-2 ::' rest , 2)
len-dec-rewrite {- P44-} ((Id "P44") :: _::_(InputChar 'S') rest) = just (ParseTree parsed-alpha-range-2 ::' rest , 2)
len-dec-rewrite {- P45-} ((Id "P45") :: _::_(InputChar 'T') rest) = just (ParseTree parsed-alpha-range-2 ::' rest , 2)
len-dec-rewrite {- P46-} ((Id "P46") :: _::_(InputChar 'U') rest) = just (ParseTree parsed-alpha-range-2 ::' rest , 2)
len-dec-rewrite {- P47-} ((Id "P47") :: _::_(InputChar 'V') rest) = just (ParseTree parsed-alpha-range-2 ::' rest , 2)
len-dec-rewrite {- P48-} ((Id "P48") :: _::_(InputChar 'W') rest) = just (ParseTree parsed-alpha-range-2 ::' rest , 2)
len-dec-rewrite {- P49-} ((Id "P49") :: _::_(InputChar 'X') rest) = just (ParseTree parsed-alpha-range-2 ::' rest , 2)
len-dec-rewrite {- P5-} ((Id "P5") :: _::_(InputChar 'f') rest) = just (ParseTree parsed-alpha-range-1 ::' rest , 2)
len-dec-rewrite {- P50-} ((Id "P50") :: _::_(InputChar 'Y') rest) = just (ParseTree parsed-alpha-range-2 ::' rest , 2)
len-dec-rewrite {- P51-} ((Id "P51") :: _::_(InputChar 'Z') rest) = just (ParseTree parsed-alpha-range-2 ::' rest , 2)
len-dec-rewrite {- P52-} ((Id "P52") :: _::_(ParseTree parsed-alpha-range-1) rest) = just (ParseTree parsed-alpha-bar-3 ::' rest , 2)
len-dec-rewrite {- P53-} ((Id "P53") :: _::_(ParseTree parsed-alpha-range-2) rest) = just (ParseTree parsed-alpha-bar-3 ::' rest , 2)
len-dec-rewrite {- P54-} ((Id "P54") :: _::_(ParseTree parsed-alpha-bar-3) rest) = just (ParseTree parsed-alpha ::' rest , 2)
len-dec-rewrite {- P55-} ((Id "P55") :: _::_(InputChar '0') rest) = just (ParseTree parsed-numone-range-4 ::' rest , 2)
len-dec-rewrite {- P56-} ((Id "P56") :: _::_(InputChar '1') rest) = just (ParseTree parsed-numone-range-4 ::' rest , 2)
len-dec-rewrite {- P57-} ((Id "P57") :: _::_(InputChar '2') rest) = just (ParseTree parsed-numone-range-4 ::' rest , 2)
len-dec-rewrite {- P58-} ((Id "P58") :: _::_(InputChar '3') rest) = just (ParseTree parsed-numone-range-4 ::' rest , 2)
len-dec-rewrite {- P59-} ((Id "P59") :: _::_(InputChar '4') rest) = just (ParseTree parsed-numone-range-4 ::' rest , 2)
len-dec-rewrite {- P6-} ((Id "P6") :: _::_(InputChar 'g') rest) = just (ParseTree parsed-alpha-range-1 ::' rest , 2)
len-dec-rewrite {- P60-} ((Id "P60") :: _::_(InputChar '5') rest) = just (ParseTree parsed-numone-range-4 ::' rest , 2)
len-dec-rewrite {- P61-} ((Id "P61") :: _::_(InputChar '6') rest) = just (ParseTree parsed-numone-range-4 ::' rest , 2)
len-dec-rewrite {- P62-} ((Id "P62") :: _::_(InputChar '7') rest) = just (ParseTree parsed-numone-range-4 ::' rest , 2)
len-dec-rewrite {- P63-} ((Id "P63") :: _::_(InputChar '8') rest) = just (ParseTree parsed-numone-range-4 ::' rest , 2)
len-dec-rewrite {- P64-} ((Id "P64") :: _::_(InputChar '9') rest) = just (ParseTree parsed-numone-range-4 ::' rest , 2)
len-dec-rewrite {- P65-} ((Id "P65") :: _::_(ParseTree parsed-numone-range-4) rest) = just (ParseTree parsed-numone ::' rest , 2)
len-dec-rewrite {- P66-} ((Id "P66") :: _::_(ParseTree parsed-numone) rest) = just (ParseTree parsed-num-plus-5 ::' rest , 2)
len-dec-rewrite {- P67-} ((Id "P67") :: (ParseTree parsed-numone) :: _::_(ParseTree parsed-num-plus-5) rest) = just (ParseTree parsed-num-plus-5 ::' rest , 3)
len-dec-rewrite {- P68-} ((Id "P68") :: _::_(ParseTree parsed-num-plus-5) rest) = just (ParseTree parsed-num ::' rest , 2)
len-dec-rewrite {- P69-} ((Id "P69") :: _::_(InputChar '_') rest) = just (ParseTree parsed-numpunct-bar-6 ::' rest , 2)
len-dec-rewrite {- P7-} ((Id "P7") :: _::_(InputChar 'h') rest) = just (ParseTree parsed-alpha-range-1 ::' rest , 2)
len-dec-rewrite {- P70-} ((Id "P70") :: _::_(InputChar '/') rest) = just (ParseTree parsed-numpunct-bar-6 ::' rest , 2)
len-dec-rewrite {- P71-} ((Id "P71") :: _::_(InputChar '#') rest) = just (ParseTree parsed-numpunct-bar-7 ::' rest , 2)
len-dec-rewrite {- P72-} ((Id "P72") :: _::_(ParseTree parsed-numpunct-bar-6) rest) = just (ParseTree parsed-numpunct-bar-7 ::' rest , 2)
len-dec-rewrite {- P73-} ((Id "P73") :: _::_(InputChar '~') rest) = just (ParseTree parsed-numpunct-bar-8 ::' rest , 2)
len-dec-rewrite {- P74-} ((Id "P74") :: _::_(ParseTree parsed-numpunct-bar-7) rest) = just (ParseTree parsed-numpunct-bar-8 ::' rest , 2)
len-dec-rewrite {- P75-} ((Id "P75") :: _::_(InputChar '-') rest) = just (ParseTree parsed-numpunct-bar-9 ::' rest , 2)
len-dec-rewrite {- P76-} ((Id "P76") :: _::_(ParseTree parsed-numpunct-bar-8) rest) = just (ParseTree parsed-numpunct-bar-9 ::' rest , 2)
len-dec-rewrite {- P77-} ((Id "P77") :: _::_(InputChar '\'') rest) = just (ParseTree parsed-numpunct-bar-10 ::' rest , 2)
len-dec-rewrite {- P78-} ((Id "P78") :: _::_(ParseTree parsed-numpunct-bar-9) rest) = just (ParseTree parsed-numpunct-bar-10 ::' rest , 2)
len-dec-rewrite {- P79-} ((Id "P79") :: _::_(ParseTree parsed-numone) rest) = just (ParseTree parsed-numpunct-bar-11 ::' rest , 2)
len-dec-rewrite {- P8-} ((Id "P8") :: _::_(InputChar 'i') rest) = just (ParseTree parsed-alpha-range-1 ::' rest , 2)
len-dec-rewrite {- P80-} ((Id "P80") :: _::_(ParseTree parsed-numpunct-bar-10) rest) = just (ParseTree parsed-numpunct-bar-11 ::' rest , 2)
len-dec-rewrite {- P81-} ((Id "P81") :: _::_(ParseTree parsed-numpunct-bar-11) rest) = just (ParseTree parsed-numpunct ::' rest , 2)
len-dec-rewrite {- P82-} ((Id "P82") :: _::_(InputChar '◂') rest) = just (ParseTree parsed-otherpunct-bar-12 ::' rest , 2)
len-dec-rewrite {- P83-} ((Id "P83") :: _::_(InputChar 'ω') rest) = just (ParseTree parsed-otherpunct-bar-12 ::' rest , 2)
len-dec-rewrite {- P84-} ((Id "P84") :: _::_(InputChar 'φ') rest) = just (ParseTree parsed-otherpunct-bar-13 ::' rest , 2)
len-dec-rewrite {- P85-} ((Id "P85") :: _::_(ParseTree parsed-otherpunct-bar-12) rest) = just (ParseTree parsed-otherpunct-bar-13 ::' rest , 2)
len-dec-rewrite {- P86-} ((Id "P86") :: _::_(InputChar 'υ') rest) = just (ParseTree parsed-otherpunct-bar-14 ::' rest , 2)
len-dec-rewrite {- P87-} ((Id "P87") :: _::_(ParseTree parsed-otherpunct-bar-13) rest) = just (ParseTree parsed-otherpunct-bar-14 ::' rest , 2)
len-dec-rewrite {- P88-} ((Id "P88") :: _::_(InputChar 'μ') rest) = just (ParseTree parsed-otherpunct-bar-15 ::' rest , 2)
len-dec-rewrite {- P89-} ((Id "P89") :: _::_(ParseTree parsed-otherpunct-bar-14) rest) = just (ParseTree parsed-otherpunct-bar-15 ::' rest , 2)
len-dec-rewrite {- P9-} ((Id "P9") :: _::_(InputChar 'j') rest) = just (ParseTree parsed-alpha-range-1 ::' rest , 2)
len-dec-rewrite {- P90-} ((Id "P90") :: _::_(InputChar 'χ') rest) = just (ParseTree parsed-otherpunct-bar-16 ::' rest , 2)
len-dec-rewrite {- P91-} ((Id "P91") :: _::_(ParseTree parsed-otherpunct-bar-15) rest) = just (ParseTree parsed-otherpunct-bar-16 ::' rest , 2)
len-dec-rewrite {- P92-} ((Id "P92") :: _::_(InputChar 'δ') rest) = just (ParseTree parsed-otherpunct-bar-17 ::' rest , 2)
len-dec-rewrite {- P93-} ((Id "P93") :: _::_(ParseTree parsed-otherpunct-bar-16) rest) = just (ParseTree parsed-otherpunct-bar-17 ::' rest , 2)
len-dec-rewrite {- P94-} ((Id "P94") :: _::_(InputChar '\"') rest) = just (ParseTree parsed-otherpunct-bar-18 ::' rest , 2)
len-dec-rewrite {- P95-} ((Id "P95") :: _::_(ParseTree parsed-otherpunct-bar-17) rest) = just (ParseTree parsed-otherpunct-bar-18 ::' rest , 2)
len-dec-rewrite {- P96-} ((Id "P96") :: _::_(InputChar '≃') rest) = just (ParseTree parsed-otherpunct-bar-19 ::' rest , 2)
len-dec-rewrite {- P97-} ((Id "P97") :: _::_(ParseTree parsed-otherpunct-bar-18) rest) = just (ParseTree parsed-otherpunct-bar-19 ::' rest , 2)
len-dec-rewrite {- P98-} ((Id "P98") :: _::_(InputChar '>') rest) = just (ParseTree parsed-otherpunct-bar-20 ::' rest , 2)
len-dec-rewrite {- P99-} ((Id "P99") :: _::_(ParseTree parsed-otherpunct-bar-19) rest) = just (ParseTree parsed-otherpunct-bar-20 ::' rest , 2)
len-dec-rewrite {- EndEntity-} (_::_(Id "EndEntity") rest) = just (ParseTree (parsed-entities (norm-entities EndEntity)) ::' rest , 1)
len-dec-rewrite {- P188-} (_::_(Id "P188") rest) = just (ParseTree parsed-comment-star-64 ::' rest , 1)
len-dec-rewrite {- Posinfo-} (_::_(Posinfo n) rest) = just (ParseTree (parsed-posinfo (ℕ-to-string n)) ::' rest , 1)
len-dec-rewrite x = nothing

rrs : rewriteRules
rrs = record { len-dec-rewrite = len-dec-rewrite }
