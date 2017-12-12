module cedille where

open import lib

open import cedille-types public
----------------------------------------------------------------------------------
-- Run-rewriting rules
----------------------------------------------------------------------------------

data gratr2-nt : Set where
  _ws-plus-77 : gratr2-nt
  _ws : gratr2-nt
  _vars : gratr2-nt
  _var-star-12 : gratr2-nt
  _var-bar-11 : gratr2-nt
  _var : gratr2-nt
  _type : gratr2-nt
  _tk : gratr2-nt
  _theta : gratr2-nt
  _term : gratr2-nt
  _start : gratr2-nt
  _rho : gratr2-nt
  _qvar : gratr2-nt
  _qkvar : gratr2-nt
  _pterm : gratr2-nt
  _posinfo : gratr2-nt
  _params : gratr2-nt
  _ows-star-78 : gratr2-nt
  _ows : gratr2-nt
  _otherpunct-bar-67 : gratr2-nt
  _otherpunct-bar-66 : gratr2-nt
  _otherpunct-bar-65 : gratr2-nt
  _otherpunct-bar-64 : gratr2-nt
  _otherpunct-bar-63 : gratr2-nt
  _otherpunct-bar-62 : gratr2-nt
  _otherpunct-bar-61 : gratr2-nt
  _otherpunct-bar-60 : gratr2-nt
  _otherpunct-bar-59 : gratr2-nt
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
  _otherpunct : gratr2-nt
  _optType : gratr2-nt
  _optTerm : gratr2-nt
  _optClass : gratr2-nt
  _optAs : gratr2-nt
  _numpunct-bar-9 : gratr2-nt
  _numpunct-bar-8 : gratr2-nt
  _numpunct-bar-7 : gratr2-nt
  _numpunct-bar-6 : gratr2-nt
  _numpunct-bar-10 : gratr2-nt
  _numpunct : gratr2-nt
  _numone-range-4 : gratr2-nt
  _numone : gratr2-nt
  _num-plus-5 : gratr2-nt
  _num : gratr2-nt
  _maybeMinus : gratr2-nt
  _maybeErased : gratr2-nt
  _maybeCheckType : gratr2-nt
  _maybeAtype : gratr2-nt
  _ltype : gratr2-nt
  _lterms : gratr2-nt
  _lterm : gratr2-nt
  _lliftingType : gratr2-nt
  _liftingType : gratr2-nt
  _leftRight : gratr2-nt
  _lam : gratr2-nt
  _kvar-star-20 : gratr2-nt
  _kvar-bar-19 : gratr2-nt
  _kvar : gratr2-nt
  _kind : gratr2-nt
  _imprt : gratr2-nt
  _imports : gratr2-nt
  _fpth-star-18 : gratr2-nt
  _fpth-plus-14 : gratr2-nt
  _fpth-bar-17 : gratr2-nt
  _fpth-bar-16 : gratr2-nt
  _fpth-bar-15 : gratr2-nt
  _fpth : gratr2-nt
  _defTermOrType : gratr2-nt
  _decl : gratr2-nt
  _comment-star-73 : gratr2-nt
  _comment : gratr2-nt
  _cmds : gratr2-nt
  _cmd : gratr2-nt
  _bvar-bar-13 : gratr2-nt
  _bvar : gratr2-nt
  _binder : gratr2-nt
  _aws-bar-76 : gratr2-nt
  _aws-bar-75 : gratr2-nt
  _aws-bar-74 : gratr2-nt
  _aws : gratr2-nt
  _atype : gratr2-nt
  _aterm : gratr2-nt
  _arrowtype : gratr2-nt
  _args : gratr2-nt
  _arg : gratr2-nt
  _anychar-bar-72 : gratr2-nt
  _anychar-bar-71 : gratr2-nt
  _anychar-bar-70 : gratr2-nt
  _anychar-bar-69 : gratr2-nt
  _anychar-bar-68 : gratr2-nt
  _anychar : gratr2-nt
  _alpha-range-2 : gratr2-nt
  _alpha-range-1 : gratr2-nt
  _alpha-bar-3 : gratr2-nt
  _alpha : gratr2-nt


gratr2-nt-eq : gratr2-nt → gratr2-nt → 𝔹
gratr2-nt-eq  _ws-plus-77 _ws-plus-77 = tt
gratr2-nt-eq  _ws _ws = tt
gratr2-nt-eq  _vars _vars = tt
gratr2-nt-eq  _var-star-12 _var-star-12 = tt
gratr2-nt-eq  _var-bar-11 _var-bar-11 = tt
gratr2-nt-eq  _var _var = tt
gratr2-nt-eq  _type _type = tt
gratr2-nt-eq  _tk _tk = tt
gratr2-nt-eq  _theta _theta = tt
gratr2-nt-eq  _term _term = tt
gratr2-nt-eq  _start _start = tt
gratr2-nt-eq  _rho _rho = tt
gratr2-nt-eq  _qvar _qvar = tt
gratr2-nt-eq  _qkvar _qkvar = tt
gratr2-nt-eq  _pterm _pterm = tt
gratr2-nt-eq  _posinfo _posinfo = tt
gratr2-nt-eq  _params _params = tt
gratr2-nt-eq  _ows-star-78 _ows-star-78 = tt
gratr2-nt-eq  _ows _ows = tt
gratr2-nt-eq  _otherpunct-bar-67 _otherpunct-bar-67 = tt
gratr2-nt-eq  _otherpunct-bar-66 _otherpunct-bar-66 = tt
gratr2-nt-eq  _otherpunct-bar-65 _otherpunct-bar-65 = tt
gratr2-nt-eq  _otherpunct-bar-64 _otherpunct-bar-64 = tt
gratr2-nt-eq  _otherpunct-bar-63 _otherpunct-bar-63 = tt
gratr2-nt-eq  _otherpunct-bar-62 _otherpunct-bar-62 = tt
gratr2-nt-eq  _otherpunct-bar-61 _otherpunct-bar-61 = tt
gratr2-nt-eq  _otherpunct-bar-60 _otherpunct-bar-60 = tt
gratr2-nt-eq  _otherpunct-bar-59 _otherpunct-bar-59 = tt
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
gratr2-nt-eq  _otherpunct _otherpunct = tt
gratr2-nt-eq  _optType _optType = tt
gratr2-nt-eq  _optTerm _optTerm = tt
gratr2-nt-eq  _optClass _optClass = tt
gratr2-nt-eq  _optAs _optAs = tt
gratr2-nt-eq  _numpunct-bar-9 _numpunct-bar-9 = tt
gratr2-nt-eq  _numpunct-bar-8 _numpunct-bar-8 = tt
gratr2-nt-eq  _numpunct-bar-7 _numpunct-bar-7 = tt
gratr2-nt-eq  _numpunct-bar-6 _numpunct-bar-6 = tt
gratr2-nt-eq  _numpunct-bar-10 _numpunct-bar-10 = tt
gratr2-nt-eq  _numpunct _numpunct = tt
gratr2-nt-eq  _numone-range-4 _numone-range-4 = tt
gratr2-nt-eq  _numone _numone = tt
gratr2-nt-eq  _num-plus-5 _num-plus-5 = tt
gratr2-nt-eq  _num _num = tt
gratr2-nt-eq  _maybeMinus _maybeMinus = tt
gratr2-nt-eq  _maybeErased _maybeErased = tt
gratr2-nt-eq  _maybeCheckType _maybeCheckType = tt
gratr2-nt-eq  _maybeAtype _maybeAtype = tt
gratr2-nt-eq  _ltype _ltype = tt
gratr2-nt-eq  _lterms _lterms = tt
gratr2-nt-eq  _lterm _lterm = tt
gratr2-nt-eq  _lliftingType _lliftingType = tt
gratr2-nt-eq  _liftingType _liftingType = tt
gratr2-nt-eq  _leftRight _leftRight = tt
gratr2-nt-eq  _lam _lam = tt
gratr2-nt-eq  _kvar-star-20 _kvar-star-20 = tt
gratr2-nt-eq  _kvar-bar-19 _kvar-bar-19 = tt
gratr2-nt-eq  _kvar _kvar = tt
gratr2-nt-eq  _kind _kind = tt
gratr2-nt-eq  _imprt _imprt = tt
gratr2-nt-eq  _imports _imports = tt
gratr2-nt-eq  _fpth-star-18 _fpth-star-18 = tt
gratr2-nt-eq  _fpth-plus-14 _fpth-plus-14 = tt
gratr2-nt-eq  _fpth-bar-17 _fpth-bar-17 = tt
gratr2-nt-eq  _fpth-bar-16 _fpth-bar-16 = tt
gratr2-nt-eq  _fpth-bar-15 _fpth-bar-15 = tt
gratr2-nt-eq  _fpth _fpth = tt
gratr2-nt-eq  _defTermOrType _defTermOrType = tt
gratr2-nt-eq  _decl _decl = tt
gratr2-nt-eq  _comment-star-73 _comment-star-73 = tt
gratr2-nt-eq  _comment _comment = tt
gratr2-nt-eq  _cmds _cmds = tt
gratr2-nt-eq  _cmd _cmd = tt
gratr2-nt-eq  _bvar-bar-13 _bvar-bar-13 = tt
gratr2-nt-eq  _bvar _bvar = tt
gratr2-nt-eq  _binder _binder = tt
gratr2-nt-eq  _aws-bar-76 _aws-bar-76 = tt
gratr2-nt-eq  _aws-bar-75 _aws-bar-75 = tt
gratr2-nt-eq  _aws-bar-74 _aws-bar-74 = tt
gratr2-nt-eq  _aws _aws = tt
gratr2-nt-eq  _atype _atype = tt
gratr2-nt-eq  _aterm _aterm = tt
gratr2-nt-eq  _arrowtype _arrowtype = tt
gratr2-nt-eq  _args _args = tt
gratr2-nt-eq  _arg _arg = tt
gratr2-nt-eq  _anychar-bar-72 _anychar-bar-72 = tt
gratr2-nt-eq  _anychar-bar-71 _anychar-bar-71 = tt
gratr2-nt-eq  _anychar-bar-70 _anychar-bar-70 = tt
gratr2-nt-eq  _anychar-bar-69 _anychar-bar-69 = tt
gratr2-nt-eq  _anychar-bar-68 _anychar-bar-68 = tt
gratr2-nt-eq  _anychar _anychar = tt
gratr2-nt-eq  _alpha-range-2 _alpha-range-2 = tt
gratr2-nt-eq  _alpha-range-1 _alpha-range-1 = tt
gratr2-nt-eq  _alpha-bar-3 _alpha-bar-3 = tt
gratr2-nt-eq  _alpha _alpha = tt
gratr2-nt-eq _ _ = ff


open import rtn gratr2-nt


cedille-start : gratr2-nt → 𝕃 gratr2-rule
cedille-start _ws-plus-77 = (just "P225" , nothing , just _ws-plus-77 , inj₁ _aws :: inj₁ _ws-plus-77 :: []) :: (just "P224" , nothing , just _ws-plus-77 , inj₁ _aws :: []) :: []
cedille-start _ws = (just "P226" , nothing , just _ws , inj₁ _ws-plus-77 :: []) :: []
cedille-start _vars = (just "VarsStart" , nothing , just _vars , inj₁ _var :: []) :: (just "VarsNext" , nothing , just _vars , inj₁ _var :: inj₁ _ws :: inj₁ _vars :: []) :: []
cedille-start _var-star-12 = (just "P85" , nothing , just _var-star-12 , inj₁ _var-bar-11 :: inj₁ _var-star-12 :: []) :: (just "P84" , nothing , just _var-star-12 , []) :: []
cedille-start _var-bar-11 = (just "P83" , nothing , just _var-bar-11 , inj₁ _numpunct :: []) :: (just "P82" , nothing , just _var-bar-11 , inj₁ _alpha :: []) :: []
cedille-start _var = (just "P86" , nothing , just _var , inj₁ _alpha :: inj₁ _var-star-12 :: []) :: []
cedille-start _type = (just "embed" , just "embed_end" , just _type , inj₁ _ltype :: []) :: (just "TpLambda" , nothing , just _type , inj₁ _posinfo :: inj₂ 'λ' :: inj₁ _ows :: inj₁ _posinfo :: inj₁ _bvar :: inj₁ _ows :: inj₂ ':' :: inj₁ _ows :: inj₁ _tk :: inj₁ _ows :: inj₂ '.' :: inj₁ _ows :: inj₁ _type :: []) :: (just "TpEq" , nothing , just _type , inj₁ _term :: inj₁ _ows :: inj₂ '≃' :: inj₁ _ows :: inj₁ _term :: []) :: (just "TpArrow" , nothing , just _type , inj₁ _ltype :: inj₁ _ows :: inj₁ _arrowtype :: inj₁ _ows :: inj₁ _type :: []) :: (just "NoSpans" , nothing , just _type , inj₂ '{' :: inj₂ '^' :: inj₁ _type :: inj₁ _posinfo :: inj₂ '^' :: inj₂ '}' :: []) :: (just "Iota" , nothing , just _type , inj₁ _posinfo :: inj₂ 'ι' :: inj₁ _ows :: inj₁ _posinfo :: inj₁ _bvar :: inj₁ _optType :: inj₁ _ows :: inj₂ '.' :: inj₁ _ows :: inj₁ _type :: []) :: (just "Abs" , nothing , just _type , inj₁ _posinfo :: inj₁ _binder :: inj₁ _ows :: inj₁ _posinfo :: inj₁ _bvar :: inj₁ _ows :: inj₂ ':' :: inj₁ _ows :: inj₁ _tk :: inj₁ _ows :: inj₂ '.' :: inj₁ _ows :: inj₁ _type :: []) :: []
cedille-start _tk = (just "Tkt" , nothing , just _tk , inj₁ _type :: []) :: (just "Tkk" , just "Tkk_end" , just _tk , inj₁ _kind :: []) :: []
cedille-start _theta = (just "AbstractVars" , nothing , just _theta , inj₂ 'θ' :: inj₂ '<' :: inj₁ _ows :: inj₁ _vars :: inj₁ _ows :: inj₂ '>' :: []) :: (just "AbstractEq" , nothing , just _theta , inj₂ 'θ' :: inj₂ '+' :: []) :: (just "Abstract" , nothing , just _theta , inj₂ 'θ' :: []) :: []
cedille-start _term = (just "embed" , just "embed_end" , just _term , inj₁ _aterm :: []) :: (just "Theta" , nothing , just _term , inj₁ _posinfo :: inj₁ _theta :: inj₁ _ws :: inj₁ _lterm :: inj₁ _ows :: inj₁ _lterms :: []) :: (just "Let" , nothing , just _term , inj₁ _posinfo :: inj₂ 'l' :: inj₂ 'e' :: inj₂ 't' :: inj₁ _ws :: inj₁ _defTermOrType :: inj₁ _ws :: inj₂ 'i' :: inj₂ 'n' :: inj₁ _ws :: inj₁ _term :: []) :: (just "Lam" , nothing , just _term , inj₁ _posinfo :: inj₁ _lam :: inj₁ _ows :: inj₁ _posinfo :: inj₁ _bvar :: inj₁ _optClass :: inj₁ _ows :: inj₂ '.' :: inj₁ _ows :: inj₁ _term :: []) :: []
cedille-start _start = (just "File" , nothing , just _start , inj₁ _posinfo :: inj₁ _ows :: inj₁ _imports :: inj₂ 'm' :: inj₂ 'o' :: inj₂ 'd' :: inj₂ 'u' :: inj₂ 'l' :: inj₂ 'e' :: inj₁ _ws :: inj₁ _qvar :: inj₁ _ows :: inj₁ _params :: inj₁ _ows :: inj₂ '.' :: inj₁ _ows :: inj₁ _cmds :: inj₁ _ows :: inj₁ _posinfo :: []) :: []
cedille-start _rho = (just "RhoPlus" , nothing , just _rho , inj₂ 'ρ' :: inj₂ '+' :: []) :: (just "RhoPlain" , nothing , just _rho , inj₂ 'ρ' :: []) :: []
cedille-start _qvar = (just "P81" , nothing , just _qvar , inj₁ _var :: inj₂ '.' :: inj₁ _qvar :: []) :: (just "P80" , nothing , just _qvar , inj₁ _var :: []) :: []
cedille-start _qkvar = (just "P102" , nothing , just _qkvar , inj₁ _var :: inj₂ '.' :: inj₁ _qkvar :: []) :: (just "P101" , nothing , just _qkvar , inj₁ _kvar :: []) :: []
cedille-start _pterm = (just "Var" , nothing , just _pterm , inj₁ _posinfo :: inj₁ _qvar :: []) :: (just "Parens" , nothing , just _pterm , inj₁ _posinfo :: inj₂ '(' :: inj₁ _ows :: inj₁ _term :: inj₁ _ows :: inj₂ ')' :: inj₁ _posinfo :: []) :: (just "IotaPair" , nothing , just _pterm , inj₁ _posinfo :: inj₂ '[' :: inj₁ _ows :: inj₁ _term :: inj₁ _ows :: inj₂ ',' :: inj₁ _ows :: inj₁ _term :: inj₁ _optTerm :: inj₁ _ows :: inj₂ ']' :: inj₁ _posinfo :: []) :: (just "Hole" , nothing , just _pterm , inj₁ _posinfo :: inj₂ '●' :: []) :: []
cedille-start _posinfo = (just "Posinfo" , nothing , just _posinfo , []) :: []
cedille-start _params = (just "ParamsNil" , nothing , just _params , []) :: (just "ParamsCons" , nothing , just _params , inj₁ _ows :: inj₁ _decl :: inj₁ _params :: []) :: []
cedille-start _ows-star-78 = (just "P228" , nothing , just _ows-star-78 , inj₁ _aws :: inj₁ _ows-star-78 :: []) :: (just "P227" , nothing , just _ows-star-78 , []) :: []
cedille-start _ows = (just "P229" , nothing , just _ows , inj₁ _ows-star-78 :: []) :: []
cedille-start _otherpunct-bar-67 = (just "P201" , nothing , just _otherpunct-bar-67 , inj₁ _otherpunct-bar-66 :: []) :: (just "P200" , nothing , just _otherpunct-bar-67 , inj₂ '|' :: []) :: []
cedille-start _otherpunct-bar-66 = (just "P199" , nothing , just _otherpunct-bar-66 , inj₁ _otherpunct-bar-65 :: []) :: (just "P198" , nothing , just _otherpunct-bar-66 , inj₂ '□' :: []) :: []
cedille-start _otherpunct-bar-65 = (just "P197" , nothing , just _otherpunct-bar-65 , inj₁ _otherpunct-bar-64 :: []) :: (just "P196" , nothing , just _otherpunct-bar-65 , inj₂ 'Π' :: []) :: []
cedille-start _otherpunct-bar-64 = (just "P195" , nothing , just _otherpunct-bar-64 , inj₁ _otherpunct-bar-63 :: []) :: (just "P194" , nothing , just _otherpunct-bar-64 , inj₂ 'ι' :: []) :: []
cedille-start _otherpunct-bar-63 = (just "P193" , nothing , just _otherpunct-bar-63 , inj₁ _otherpunct-bar-62 :: []) :: (just "P192" , nothing , just _otherpunct-bar-63 , inj₂ 'λ' :: []) :: []
cedille-start _otherpunct-bar-62 = (just "P191" , nothing , just _otherpunct-bar-62 , inj₁ _otherpunct-bar-61 :: []) :: (just "P190" , nothing , just _otherpunct-bar-62 , inj₂ '∀' :: []) :: []
cedille-start _otherpunct-bar-61 = (just "P189" , nothing , just _otherpunct-bar-61 , inj₁ _otherpunct-bar-60 :: []) :: (just "P188" , nothing , just _otherpunct-bar-61 , inj₂ 'π' :: []) :: []
cedille-start _otherpunct-bar-60 = (just "P187" , nothing , just _otherpunct-bar-60 , inj₁ _otherpunct-bar-59 :: []) :: (just "P186" , nothing , just _otherpunct-bar-60 , inj₂ '★' :: []) :: []
cedille-start _otherpunct-bar-59 = (just "P185" , nothing , just _otherpunct-bar-59 , inj₁ _otherpunct-bar-58 :: []) :: (just "P184" , nothing , just _otherpunct-bar-59 , inj₂ '☆' :: []) :: []
cedille-start _otherpunct-bar-58 = (just "P183" , nothing , just _otherpunct-bar-58 , inj₁ _otherpunct-bar-57 :: []) :: (just "P182" , nothing , just _otherpunct-bar-58 , inj₂ '·' :: []) :: []
cedille-start _otherpunct-bar-57 = (just "P181" , nothing , just _otherpunct-bar-57 , inj₁ _otherpunct-bar-56 :: []) :: (just "P180" , nothing , just _otherpunct-bar-57 , inj₂ '⇐' :: []) :: []
cedille-start _otherpunct-bar-56 = (just "P179" , nothing , just _otherpunct-bar-56 , inj₁ _otherpunct-bar-55 :: []) :: (just "P178" , nothing , just _otherpunct-bar-56 , inj₂ '➔' :: []) :: []
cedille-start _otherpunct-bar-55 = (just "P177" , nothing , just _otherpunct-bar-55 , inj₁ _otherpunct-bar-54 :: []) :: (just "P176" , nothing , just _otherpunct-bar-55 , inj₂ '➾' :: []) :: []
cedille-start _otherpunct-bar-54 = (just "P175" , nothing , just _otherpunct-bar-54 , inj₁ _otherpunct-bar-53 :: []) :: (just "P174" , nothing , just _otherpunct-bar-54 , inj₂ '↑' :: []) :: []
cedille-start _otherpunct-bar-53 = (just "P173" , nothing , just _otherpunct-bar-53 , inj₁ _otherpunct-bar-52 :: []) :: (just "P172" , nothing , just _otherpunct-bar-53 , inj₂ '●' :: []) :: []
cedille-start _otherpunct-bar-52 = (just "P171" , nothing , just _otherpunct-bar-52 , inj₁ _otherpunct-bar-51 :: []) :: (just "P170" , nothing , just _otherpunct-bar-52 , inj₂ '(' :: []) :: []
cedille-start _otherpunct-bar-51 = (just "P169" , nothing , just _otherpunct-bar-51 , inj₁ _otherpunct-bar-50 :: []) :: (just "P168" , nothing , just _otherpunct-bar-51 , inj₂ ')' :: []) :: []
cedille-start _otherpunct-bar-50 = (just "P167" , nothing , just _otherpunct-bar-50 , inj₁ _otherpunct-bar-49 :: []) :: (just "P166" , nothing , just _otherpunct-bar-50 , inj₂ ':' :: []) :: []
cedille-start _otherpunct-bar-49 = (just "P165" , nothing , just _otherpunct-bar-49 , inj₁ _otherpunct-bar-48 :: []) :: (just "P164" , nothing , just _otherpunct-bar-49 , inj₂ '.' :: []) :: []
cedille-start _otherpunct-bar-48 = (just "P163" , nothing , just _otherpunct-bar-48 , inj₁ _otherpunct-bar-47 :: []) :: (just "P162" , nothing , just _otherpunct-bar-48 , inj₂ '[' :: []) :: []
cedille-start _otherpunct-bar-47 = (just "P161" , nothing , just _otherpunct-bar-47 , inj₁ _otherpunct-bar-46 :: []) :: (just "P160" , nothing , just _otherpunct-bar-47 , inj₂ ']' :: []) :: []
cedille-start _otherpunct-bar-46 = (just "P159" , nothing , just _otherpunct-bar-46 , inj₁ _otherpunct-bar-45 :: []) :: (just "P158" , nothing , just _otherpunct-bar-46 , inj₂ ',' :: []) :: []
cedille-start _otherpunct-bar-45 = (just "P157" , nothing , just _otherpunct-bar-45 , inj₁ _otherpunct-bar-44 :: []) :: (just "P156" , nothing , just _otherpunct-bar-45 , inj₂ '!' :: []) :: []
cedille-start _otherpunct-bar-44 = (just "P155" , nothing , just _otherpunct-bar-44 , inj₁ _otherpunct-bar-43 :: []) :: (just "P154" , nothing , just _otherpunct-bar-44 , inj₂ '{' :: []) :: []
cedille-start _otherpunct-bar-43 = (just "P153" , nothing , just _otherpunct-bar-43 , inj₁ _otherpunct-bar-42 :: []) :: (just "P152" , nothing , just _otherpunct-bar-43 , inj₂ '}' :: []) :: []
cedille-start _otherpunct-bar-42 = (just "P151" , nothing , just _otherpunct-bar-42 , inj₁ _otherpunct-bar-41 :: []) :: (just "P150" , nothing , just _otherpunct-bar-42 , inj₂ '⇒' :: []) :: []
cedille-start _otherpunct-bar-41 = (just "P149" , nothing , just _otherpunct-bar-41 , inj₁ _otherpunct-bar-40 :: []) :: (just "P148" , nothing , just _otherpunct-bar-41 , inj₂ '?' :: []) :: []
cedille-start _otherpunct-bar-40 = (just "P147" , nothing , just _otherpunct-bar-40 , inj₁ _otherpunct-bar-39 :: []) :: (just "P146" , nothing , just _otherpunct-bar-40 , inj₂ 'Λ' :: []) :: []
cedille-start _otherpunct-bar-39 = (just "P145" , nothing , just _otherpunct-bar-39 , inj₁ _otherpunct-bar-38 :: []) :: (just "P144" , nothing , just _otherpunct-bar-39 , inj₂ 'ρ' :: []) :: []
cedille-start _otherpunct-bar-38 = (just "P143" , nothing , just _otherpunct-bar-38 , inj₁ _otherpunct-bar-37 :: []) :: (just "P142" , nothing , just _otherpunct-bar-38 , inj₂ 'ε' :: []) :: []
cedille-start _otherpunct-bar-37 = (just "P141" , nothing , just _otherpunct-bar-37 , inj₁ _otherpunct-bar-36 :: []) :: (just "P140" , nothing , just _otherpunct-bar-37 , inj₂ 'β' :: []) :: []
cedille-start _otherpunct-bar-36 = (just "P139" , nothing , just _otherpunct-bar-36 , inj₁ _otherpunct-bar-35 :: []) :: (just "P138" , nothing , just _otherpunct-bar-36 , inj₂ '-' :: []) :: []
cedille-start _otherpunct-bar-35 = (just "P137" , nothing , just _otherpunct-bar-35 , inj₁ _otherpunct-bar-34 :: []) :: (just "P136" , nothing , just _otherpunct-bar-35 , inj₂ '𝒌' :: []) :: []
cedille-start _otherpunct-bar-34 = (just "P135" , nothing , just _otherpunct-bar-34 , inj₁ _otherpunct-bar-33 :: []) :: (just "P134" , nothing , just _otherpunct-bar-34 , inj₂ '=' :: []) :: []
cedille-start _otherpunct-bar-33 = (just "P133" , nothing , just _otherpunct-bar-33 , inj₁ _otherpunct-bar-32 :: []) :: (just "P132" , nothing , just _otherpunct-bar-33 , inj₂ 'ς' :: []) :: []
cedille-start _otherpunct-bar-32 = (just "P131" , nothing , just _otherpunct-bar-32 , inj₁ _otherpunct-bar-31 :: []) :: (just "P130" , nothing , just _otherpunct-bar-32 , inj₂ 'θ' :: []) :: []
cedille-start _otherpunct-bar-31 = (just "P129" , nothing , just _otherpunct-bar-31 , inj₁ _otherpunct-bar-30 :: []) :: (just "P128" , nothing , just _otherpunct-bar-31 , inj₂ '+' :: []) :: []
cedille-start _otherpunct-bar-30 = (just "P127" , nothing , just _otherpunct-bar-30 , inj₁ _otherpunct-bar-29 :: []) :: (just "P126" , nothing , just _otherpunct-bar-30 , inj₂ '<' :: []) :: []
cedille-start _otherpunct-bar-29 = (just "P125" , nothing , just _otherpunct-bar-29 , inj₁ _otherpunct-bar-28 :: []) :: (just "P124" , nothing , just _otherpunct-bar-29 , inj₂ '>' :: []) :: []
cedille-start _otherpunct-bar-28 = (just "P123" , nothing , just _otherpunct-bar-28 , inj₁ _otherpunct-bar-27 :: []) :: (just "P122" , nothing , just _otherpunct-bar-28 , inj₂ '≃' :: []) :: []
cedille-start _otherpunct-bar-27 = (just "P121" , nothing , just _otherpunct-bar-27 , inj₁ _otherpunct-bar-26 :: []) :: (just "P120" , nothing , just _otherpunct-bar-27 , inj₂ '\"' :: []) :: []
cedille-start _otherpunct-bar-26 = (just "P119" , nothing , just _otherpunct-bar-26 , inj₁ _otherpunct-bar-25 :: []) :: (just "P118" , nothing , just _otherpunct-bar-26 , inj₂ 'δ' :: []) :: []
cedille-start _otherpunct-bar-25 = (just "P117" , nothing , just _otherpunct-bar-25 , inj₁ _otherpunct-bar-24 :: []) :: (just "P116" , nothing , just _otherpunct-bar-25 , inj₂ 'χ' :: []) :: []
cedille-start _otherpunct-bar-24 = (just "P115" , nothing , just _otherpunct-bar-24 , inj₁ _otherpunct-bar-23 :: []) :: (just "P114" , nothing , just _otherpunct-bar-24 , inj₂ 'μ' :: []) :: []
cedille-start _otherpunct-bar-23 = (just "P113" , nothing , just _otherpunct-bar-23 , inj₁ _otherpunct-bar-22 :: []) :: (just "P112" , nothing , just _otherpunct-bar-23 , inj₂ 'υ' :: []) :: []
cedille-start _otherpunct-bar-22 = (just "P111" , nothing , just _otherpunct-bar-22 , inj₁ _otherpunct-bar-21 :: []) :: (just "P110" , nothing , just _otherpunct-bar-22 , inj₂ 'φ' :: []) :: []
cedille-start _otherpunct-bar-21 = (just "P109" , nothing , just _otherpunct-bar-21 , inj₂ 'ω' :: []) :: (just "P108" , nothing , just _otherpunct-bar-21 , inj₂ '◂' :: []) :: []
cedille-start _otherpunct = (just "P202" , nothing , just _otherpunct , inj₁ _otherpunct-bar-67 :: []) :: []
cedille-start _optType = (just "SomeType" , nothing , just _optType , inj₁ _ows :: inj₂ ':' :: inj₁ _ows :: inj₁ _type :: []) :: (just "NoType" , nothing , just _optType , []) :: []
cedille-start _optTerm = (just "SomeTerm" , nothing , just _optTerm , inj₁ _ows :: inj₂ '{' :: inj₁ _ows :: inj₁ _term :: inj₁ _ows :: inj₂ '}' :: inj₁ _posinfo :: []) :: (just "NoTerm" , nothing , just _optTerm , []) :: []
cedille-start _optClass = (just "SomeClass" , nothing , just _optClass , inj₁ _ows :: inj₂ ':' :: inj₁ _ows :: inj₁ _tk :: []) :: (just "NoClass" , nothing , just _optClass , []) :: []
cedille-start _optAs = (just "SomeOptAs" , nothing , just _optAs , inj₁ _ows :: inj₂ 'a' :: inj₂ 's' :: inj₁ _ws :: inj₁ _var :: []) :: (just "NoOptAs" , nothing , just _optAs , []) :: []
cedille-start _numpunct-bar-9 = (just "P76" , nothing , just _numpunct-bar-9 , inj₁ _numpunct-bar-8 :: []) :: (just "P75" , nothing , just _numpunct-bar-9 , inj₂ '\'' :: []) :: []
cedille-start _numpunct-bar-8 = (just "P74" , nothing , just _numpunct-bar-8 , inj₁ _numpunct-bar-7 :: []) :: (just "P73" , nothing , just _numpunct-bar-8 , inj₂ '-' :: []) :: []
cedille-start _numpunct-bar-7 = (just "P72" , nothing , just _numpunct-bar-7 , inj₁ _numpunct-bar-6 :: []) :: (just "P71" , nothing , just _numpunct-bar-7 , inj₂ '~' :: []) :: []
cedille-start _numpunct-bar-6 = (just "P70" , nothing , just _numpunct-bar-6 , inj₂ '_' :: []) :: (just "P69" , nothing , just _numpunct-bar-6 , inj₂ '#' :: []) :: []
cedille-start _numpunct-bar-10 = (just "P78" , nothing , just _numpunct-bar-10 , inj₁ _numpunct-bar-9 :: []) :: (just "P77" , nothing , just _numpunct-bar-10 , inj₁ _numone :: []) :: []
cedille-start _numpunct = (just "P79" , nothing , just _numpunct , inj₁ _numpunct-bar-10 :: []) :: []
cedille-start _numone-range-4 = (just "P64" , nothing , just _numone-range-4 , inj₂ '9' :: []) :: (just "P63" , nothing , just _numone-range-4 , inj₂ '8' :: []) :: (just "P62" , nothing , just _numone-range-4 , inj₂ '7' :: []) :: (just "P61" , nothing , just _numone-range-4 , inj₂ '6' :: []) :: (just "P60" , nothing , just _numone-range-4 , inj₂ '5' :: []) :: (just "P59" , nothing , just _numone-range-4 , inj₂ '4' :: []) :: (just "P58" , nothing , just _numone-range-4 , inj₂ '3' :: []) :: (just "P57" , nothing , just _numone-range-4 , inj₂ '2' :: []) :: (just "P56" , nothing , just _numone-range-4 , inj₂ '1' :: []) :: (just "P55" , nothing , just _numone-range-4 , inj₂ '0' :: []) :: []
cedille-start _numone = (just "P65" , nothing , just _numone , inj₁ _numone-range-4 :: []) :: []
cedille-start _num-plus-5 = (just "P67" , nothing , just _num-plus-5 , inj₁ _numone :: inj₁ _num-plus-5 :: []) :: (just "P66" , nothing , just _num-plus-5 , inj₁ _numone :: []) :: []
cedille-start _num = (just "P68" , nothing , just _num , inj₁ _num-plus-5 :: []) :: []
cedille-start _maybeMinus = (just "EpsHnf" , nothing , just _maybeMinus , []) :: (just "EpsHanf" , nothing , just _maybeMinus , inj₂ '-' :: []) :: []
cedille-start _maybeErased = (just "NotErased" , nothing , just _maybeErased , []) :: (just "Erased" , nothing , just _maybeErased , inj₂ '-' :: inj₁ _ows :: []) :: []
cedille-start _maybeCheckType = (just "Type" , nothing , just _maybeCheckType , inj₁ _ows :: inj₂ '◂' :: inj₁ _ows :: inj₁ _type :: []) :: (just "NoCheckType" , nothing , just _maybeCheckType , []) :: []
cedille-start _maybeAtype = (just "NoAtype" , nothing , just _maybeAtype , []) :: (just "Atype" , nothing , just _maybeAtype , inj₁ _ows :: inj₁ _atype :: []) :: []
cedille-start _ltype = (just "embed" , nothing , just _ltype , inj₁ _atype :: []) :: (just "Lft" , nothing , just _ltype , inj₁ _posinfo :: inj₂ '↑' :: inj₁ _ows :: inj₁ _posinfo :: inj₁ _var :: inj₁ _ows :: inj₂ '.' :: inj₁ _ows :: inj₁ _term :: inj₁ _ows :: inj₂ ':' :: inj₁ _ows :: inj₁ _lliftingType :: []) :: []
cedille-start _lterms = (just "LtermsNil" , nothing , just _lterms , inj₁ _posinfo :: []) :: (just "LtermsCons" , nothing , just _lterms , inj₁ _ws :: inj₁ _maybeErased :: inj₁ _lterm :: inj₁ _lterms :: []) :: []
cedille-start _lterm = (just "embed" , just "embed_end" , just _lterm , inj₁ _pterm :: []) :: (just "Sigma" , nothing , just _lterm , inj₁ _posinfo :: inj₂ 'ς' :: inj₁ _ows :: inj₁ _lterm :: []) :: (just "Rho" , nothing , just _lterm , inj₁ _posinfo :: inj₁ _rho :: inj₁ _ows :: inj₁ _lterm :: inj₁ _ows :: inj₂ '-' :: inj₁ _ows :: inj₁ _lterm :: []) :: (just "Epsilon" , nothing , just _lterm , inj₁ _posinfo :: inj₂ 'ε' :: inj₁ _leftRight :: inj₁ _maybeMinus :: inj₁ _ows :: inj₁ _lterm :: []) :: (just "Chi" , nothing , just _lterm , inj₁ _posinfo :: inj₂ 'χ' :: inj₁ _maybeAtype :: inj₁ _ows :: inj₂ '-' :: inj₁ _ows :: inj₁ _lterm :: []) :: (just "Beta" , nothing , just _lterm , inj₁ _posinfo :: inj₂ 'β' :: inj₁ _optTerm :: []) :: []
cedille-start _lliftingType = (just "LiftStar" , nothing , just _lliftingType , inj₁ _posinfo :: inj₂ '☆' :: []) :: (just "LiftParens" , nothing , just _lliftingType , inj₁ _posinfo :: inj₂ '(' :: inj₁ _ows :: inj₁ _liftingType :: inj₁ _ows :: inj₂ ')' :: inj₁ _posinfo :: []) :: []
cedille-start _liftingType = (just "embed" , nothing , just _liftingType , inj₁ _lliftingType :: []) :: (just "LiftTpArrow" , nothing , just _liftingType , inj₁ _type :: inj₁ _ows :: inj₂ '➔' :: inj₁ _ows :: inj₁ _liftingType :: []) :: (just "LiftPi" , nothing , just _liftingType , inj₁ _posinfo :: inj₂ 'Π' :: inj₁ _ows :: inj₁ _bvar :: inj₁ _ows :: inj₂ ':' :: inj₁ _ows :: inj₁ _type :: inj₁ _ows :: inj₂ '.' :: inj₁ _ows :: inj₁ _liftingType :: []) :: []
cedille-start _leftRight = (just "Right" , nothing , just _leftRight , inj₂ 'r' :: []) :: (just "Left" , nothing , just _leftRight , inj₂ 'l' :: []) :: (just "Both" , nothing , just _leftRight , []) :: []
cedille-start _lam = (just "KeptLambda" , nothing , just _lam , inj₂ 'λ' :: []) :: (just "ErasedLambda" , nothing , just _lam , inj₂ 'Λ' :: []) :: []
cedille-start _kvar-star-20 = (just "P106" , nothing , just _kvar-star-20 , inj₁ _kvar-bar-19 :: inj₁ _kvar-star-20 :: []) :: (just "P105" , nothing , just _kvar-star-20 , []) :: []
cedille-start _kvar-bar-19 = (just "P104" , nothing , just _kvar-bar-19 , inj₁ _numpunct :: []) :: (just "P103" , nothing , just _kvar-bar-19 , inj₁ _alpha :: []) :: []
cedille-start _kvar = (just "P107" , nothing , just _kvar , inj₂ '𝒌' :: inj₁ _kvar-star-20 :: []) :: []
cedille-start _kind = (just "Star" , nothing , just _kind , inj₁ _posinfo :: inj₂ '★' :: []) :: (just "KndVar" , nothing , just _kind , inj₁ _posinfo :: inj₁ _qkvar :: inj₁ _args :: []) :: (just "KndTpArrow" , nothing , just _kind , inj₁ _ltype :: inj₁ _ows :: inj₂ '➔' :: inj₁ _ows :: inj₁ _kind :: []) :: (just "KndPi" , nothing , just _kind , inj₁ _posinfo :: inj₂ 'Π' :: inj₁ _ows :: inj₁ _posinfo :: inj₁ _bvar :: inj₁ _ows :: inj₂ ':' :: inj₁ _ows :: inj₁ _tk :: inj₁ _ows :: inj₂ '.' :: inj₁ _ows :: inj₁ _kind :: []) :: (just "KndParens" , nothing , just _kind , inj₁ _posinfo :: inj₂ '(' :: inj₁ _ows :: inj₁ _kind :: inj₁ _ows :: inj₂ ')' :: inj₁ _posinfo :: []) :: []
cedille-start _imprt = (just "Import" , nothing , just _imprt , inj₁ _posinfo :: inj₂ 'i' :: inj₂ 'm' :: inj₂ 'p' :: inj₂ 'o' :: inj₂ 'r' :: inj₂ 't' :: inj₁ _ws :: inj₁ _fpth :: inj₁ _optAs :: inj₁ _args :: inj₁ _ows :: inj₂ '.' :: inj₁ _posinfo :: []) :: []
cedille-start _imports = (just "ImportsStart" , nothing , just _imports , []) :: (just "ImportsNext" , nothing , just _imports , inj₁ _imprt :: inj₁ _ows :: inj₁ _imports :: []) :: []
cedille-start _fpth-star-18 = (just "P99" , nothing , just _fpth-star-18 , inj₁ _fpth-bar-17 :: inj₁ _fpth-star-18 :: []) :: (just "P98" , nothing , just _fpth-star-18 , []) :: []
cedille-start _fpth-plus-14 = (just "P91" , nothing , just _fpth-plus-14 , inj₂ '.' :: inj₂ '.' :: inj₂ '/' :: inj₁ _fpth-plus-14 :: []) :: (just "P90" , nothing , just _fpth-plus-14 , inj₂ '.' :: inj₂ '.' :: inj₂ '/' :: []) :: []
cedille-start _fpth-bar-17 = (just "P97" , nothing , just _fpth-bar-17 , inj₁ _fpth-bar-16 :: []) :: (just "P96" , nothing , just _fpth-bar-17 , inj₁ _alpha :: []) :: []
cedille-start _fpth-bar-16 = (just "P95" , nothing , just _fpth-bar-16 , inj₂ '/' :: []) :: (just "P94" , nothing , just _fpth-bar-16 , inj₁ _numpunct :: []) :: []
cedille-start _fpth-bar-15 = (just "P93" , nothing , just _fpth-bar-15 , inj₁ _fpth-plus-14 :: []) :: (just "P92" , nothing , just _fpth-bar-15 , inj₁ _alpha :: []) :: []
cedille-start _fpth = (just "P100" , nothing , just _fpth , inj₁ _fpth-bar-15 :: inj₁ _fpth-star-18 :: []) :: []
cedille-start _defTermOrType = (just "DefType" , nothing , just _defTermOrType , inj₁ _posinfo :: inj₁ _var :: inj₁ _ows :: inj₂ '◂' :: inj₁ _ows :: inj₁ _kind :: inj₁ _ows :: inj₂ '=' :: inj₁ _ows :: inj₁ _type :: []) :: (just "DefTerm" , nothing , just _defTermOrType , inj₁ _posinfo :: inj₁ _var :: inj₁ _maybeCheckType :: inj₁ _ows :: inj₂ '=' :: inj₁ _ows :: inj₁ _term :: []) :: []
cedille-start _decl = (just "Decl" , nothing , just _decl , inj₁ _posinfo :: inj₂ '(' :: inj₁ _ows :: inj₁ _posinfo :: inj₁ _bvar :: inj₁ _ows :: inj₂ ':' :: inj₁ _ows :: inj₁ _tk :: inj₁ _ows :: inj₂ ')' :: inj₁ _posinfo :: []) :: []
cedille-start _comment-star-73 = (just "P215" , nothing , just _comment-star-73 , inj₁ _anychar :: inj₁ _comment-star-73 :: []) :: (just "P214" , nothing , just _comment-star-73 , []) :: []
cedille-start _comment = (just "P216" , nothing , just _comment , inj₂ '%' :: inj₁ _comment-star-73 :: inj₂ '\n' :: []) :: []
cedille-start _cmds = (just "CmdsStart" , nothing , just _cmds , []) :: (just "CmdsNext" , nothing , just _cmds , inj₁ _cmd :: inj₁ _ws :: inj₁ _cmds :: []) :: []
cedille-start _cmd = (just "ImportCmd" , nothing , just _cmd , inj₁ _imprt :: []) :: (just "DefTermOrType" , nothing , just _cmd , inj₁ _defTermOrType :: inj₁ _ows :: inj₂ '.' :: inj₁ _posinfo :: []) :: (just "DefKind" , nothing , just _cmd , inj₁ _posinfo :: inj₁ _kvar :: inj₁ _params :: inj₁ _ows :: inj₂ '=' :: inj₁ _ows :: inj₁ _kind :: inj₁ _ows :: inj₂ '.' :: inj₁ _posinfo :: []) :: []
cedille-start _bvar-bar-13 = (just "P88" , nothing , just _bvar-bar-13 , inj₁ _var :: []) :: (just "P87" , nothing , just _bvar-bar-13 , inj₂ '_' :: []) :: []
cedille-start _bvar = (just "P89" , nothing , just _bvar , inj₁ _bvar-bar-13 :: []) :: []
cedille-start _binder = (just "Pi" , nothing , just _binder , inj₂ 'Π' :: []) :: (just "All" , nothing , just _binder , inj₂ '∀' :: []) :: []
cedille-start _aws-bar-76 = (just "P222" , nothing , just _aws-bar-76 , inj₁ _aws-bar-75 :: []) :: (just "P221" , nothing , just _aws-bar-76 , inj₂ '\n' :: []) :: []
cedille-start _aws-bar-75 = (just "P220" , nothing , just _aws-bar-75 , inj₁ _aws-bar-74 :: []) :: (just "P219" , nothing , just _aws-bar-75 , inj₂ '\t' :: []) :: []
cedille-start _aws-bar-74 = (just "P218" , nothing , just _aws-bar-74 , inj₁ _comment :: []) :: (just "P217" , nothing , just _aws-bar-74 , inj₂ ' ' :: []) :: []
cedille-start _aws = (just "P223" , nothing , just _aws , inj₁ _aws-bar-76 :: []) :: []
cedille-start _atype = (just "TpVar" , nothing , just _atype , inj₁ _posinfo :: inj₁ _qvar :: []) :: (just "TpParens" , nothing , just _atype , inj₁ _posinfo :: inj₂ '(' :: inj₁ _ows :: inj₁ _type :: inj₁ _ows :: inj₂ ')' :: inj₁ _posinfo :: []) :: (just "TpHole" , nothing , just _atype , inj₁ _posinfo :: inj₂ '●' :: []) :: []
cedille-start _aterm = (just "embed" , nothing , just _aterm , inj₁ _lterm :: []) :: []
cedille-start _arrowtype = (just "UnerasedArrow" , nothing , just _arrowtype , inj₂ '➔' :: []) :: (just "ErasedArrow" , nothing , just _arrowtype , inj₂ '➾' :: []) :: []
cedille-start _args = (just "ArgsNil" , nothing , just _args , inj₁ _posinfo :: []) :: (just "ArgsCons" , nothing , just _args , inj₁ _arg :: inj₁ _args :: []) :: []
cedille-start _arg = (just "TypeArg" , nothing , just _arg , inj₁ _ows :: inj₂ '·' :: inj₁ _ws :: inj₁ _atype :: []) :: (just "TermArg" , nothing , just _arg , inj₁ _ws :: inj₁ _lterm :: []) :: []
cedille-start _anychar-bar-72 = (just "P212" , nothing , just _anychar-bar-72 , inj₁ _anychar-bar-71 :: []) :: (just "P211" , nothing , just _anychar-bar-72 , inj₁ _alpha :: []) :: []
cedille-start _anychar-bar-71 = (just "P210" , nothing , just _anychar-bar-71 , inj₁ _anychar-bar-70 :: []) :: (just "P209" , nothing , just _anychar-bar-71 , inj₁ _numpunct :: []) :: []
cedille-start _anychar-bar-70 = (just "P208" , nothing , just _anychar-bar-70 , inj₁ _anychar-bar-69 :: []) :: (just "P207" , nothing , just _anychar-bar-70 , inj₂ '\t' :: []) :: []
cedille-start _anychar-bar-69 = (just "P206" , nothing , just _anychar-bar-69 , inj₁ _anychar-bar-68 :: []) :: (just "P205" , nothing , just _anychar-bar-69 , inj₂ ' ' :: []) :: []
cedille-start _anychar-bar-68 = (just "P204" , nothing , just _anychar-bar-68 , inj₁ _otherpunct :: []) :: (just "P203" , nothing , just _anychar-bar-68 , inj₂ '%' :: []) :: []
cedille-start _anychar = (just "P213" , nothing , just _anychar , inj₁ _anychar-bar-72 :: []) :: []
cedille-start _alpha-range-2 = (just "P51" , nothing , just _alpha-range-2 , inj₂ 'Z' :: []) :: (just "P50" , nothing , just _alpha-range-2 , inj₂ 'Y' :: []) :: (just "P49" , nothing , just _alpha-range-2 , inj₂ 'X' :: []) :: (just "P48" , nothing , just _alpha-range-2 , inj₂ 'W' :: []) :: (just "P47" , nothing , just _alpha-range-2 , inj₂ 'V' :: []) :: (just "P46" , nothing , just _alpha-range-2 , inj₂ 'U' :: []) :: (just "P45" , nothing , just _alpha-range-2 , inj₂ 'T' :: []) :: (just "P44" , nothing , just _alpha-range-2 , inj₂ 'S' :: []) :: (just "P43" , nothing , just _alpha-range-2 , inj₂ 'R' :: []) :: (just "P42" , nothing , just _alpha-range-2 , inj₂ 'Q' :: []) :: (just "P41" , nothing , just _alpha-range-2 , inj₂ 'P' :: []) :: (just "P40" , nothing , just _alpha-range-2 , inj₂ 'O' :: []) :: (just "P39" , nothing , just _alpha-range-2 , inj₂ 'N' :: []) :: (just "P38" , nothing , just _alpha-range-2 , inj₂ 'M' :: []) :: (just "P37" , nothing , just _alpha-range-2 , inj₂ 'L' :: []) :: (just "P36" , nothing , just _alpha-range-2 , inj₂ 'K' :: []) :: (just "P35" , nothing , just _alpha-range-2 , inj₂ 'J' :: []) :: (just "P34" , nothing , just _alpha-range-2 , inj₂ 'I' :: []) :: (just "P33" , nothing , just _alpha-range-2 , inj₂ 'H' :: []) :: (just "P32" , nothing , just _alpha-range-2 , inj₂ 'G' :: []) :: (just "P31" , nothing , just _alpha-range-2 , inj₂ 'F' :: []) :: (just "P30" , nothing , just _alpha-range-2 , inj₂ 'E' :: []) :: (just "P29" , nothing , just _alpha-range-2 , inj₂ 'D' :: []) :: (just "P28" , nothing , just _alpha-range-2 , inj₂ 'C' :: []) :: (just "P27" , nothing , just _alpha-range-2 , inj₂ 'B' :: []) :: (just "P26" , nothing , just _alpha-range-2 , inj₂ 'A' :: []) :: []
cedille-start _alpha-range-1 = (just "P9" , nothing , just _alpha-range-1 , inj₂ 'j' :: []) :: (just "P8" , nothing , just _alpha-range-1 , inj₂ 'i' :: []) :: (just "P7" , nothing , just _alpha-range-1 , inj₂ 'h' :: []) :: (just "P6" , nothing , just _alpha-range-1 , inj₂ 'g' :: []) :: (just "P5" , nothing , just _alpha-range-1 , inj₂ 'f' :: []) :: (just "P4" , nothing , just _alpha-range-1 , inj₂ 'e' :: []) :: (just "P3" , nothing , just _alpha-range-1 , inj₂ 'd' :: []) :: (just "P25" , nothing , just _alpha-range-1 , inj₂ 'z' :: []) :: (just "P24" , nothing , just _alpha-range-1 , inj₂ 'y' :: []) :: (just "P23" , nothing , just _alpha-range-1 , inj₂ 'x' :: []) :: (just "P22" , nothing , just _alpha-range-1 , inj₂ 'w' :: []) :: (just "P21" , nothing , just _alpha-range-1 , inj₂ 'v' :: []) :: (just "P20" , nothing , just _alpha-range-1 , inj₂ 'u' :: []) :: (just "P2" , nothing , just _alpha-range-1 , inj₂ 'c' :: []) :: (just "P19" , nothing , just _alpha-range-1 , inj₂ 't' :: []) :: (just "P18" , nothing , just _alpha-range-1 , inj₂ 's' :: []) :: (just "P17" , nothing , just _alpha-range-1 , inj₂ 'r' :: []) :: (just "P16" , nothing , just _alpha-range-1 , inj₂ 'q' :: []) :: (just "P15" , nothing , just _alpha-range-1 , inj₂ 'p' :: []) :: (just "P14" , nothing , just _alpha-range-1 , inj₂ 'o' :: []) :: (just "P13" , nothing , just _alpha-range-1 , inj₂ 'n' :: []) :: (just "P12" , nothing , just _alpha-range-1 , inj₂ 'm' :: []) :: (just "P11" , nothing , just _alpha-range-1 , inj₂ 'l' :: []) :: (just "P10" , nothing , just _alpha-range-1 , inj₂ 'k' :: []) :: (just "P1" , nothing , just _alpha-range-1 , inj₂ 'b' :: []) :: (just "P0" , nothing , just _alpha-range-1 , inj₂ 'a' :: []) :: []
cedille-start _alpha-bar-3 = (just "P53" , nothing , just _alpha-bar-3 , inj₁ _alpha-range-2 :: []) :: (just "P52" , nothing , just _alpha-bar-3 , inj₁ _alpha-range-1 :: []) :: []
cedille-start _alpha = (just "P54" , nothing , just _alpha , inj₁ _alpha-bar-3 :: []) :: []


cedille-return : maybe gratr2-nt → 𝕃 gratr2-rule
cedille-return (just _pterm) = (nothing , nothing , just _pterm , inj₁ _ows :: inj₂ '.' :: inj₁ _ows :: inj₁ _num :: inj₁ _posinfo :: []) :: []
cedille-return (just _ltype) = (nothing , nothing , just _ltype , inj₁ _ws :: inj₁ _lterm :: []) :: (nothing , nothing , just _ltype , inj₁ _ws :: inj₂ '·' :: inj₁ _ws :: inj₁ _atype :: []) :: []
cedille-return (just _liftingType) = (nothing , nothing , just _liftingType , inj₁ _ows :: inj₂ '➔' :: inj₁ _ows :: inj₁ _liftingType :: []) :: []
cedille-return (just _kind) = (nothing , nothing , just _kind , inj₁ _ows :: inj₂ '➔' :: inj₁ _ows :: inj₁ _kind :: []) :: []
cedille-return (just _aterm) = (nothing , nothing , just _aterm , inj₁ _ws :: inj₂ '·' :: inj₁ _ws :: inj₁ _atype :: []) :: (nothing , nothing , just _aterm , inj₁ _ws :: inj₁ _maybeErased :: inj₁ _aterm :: []) :: []
cedille-return _ = []

cedille-rtn : gratr2-rtn
cedille-rtn = record { start = _start ; _eq_ = gratr2-nt-eq ; gratr2-start = cedille-start ; gratr2-return = cedille-return }

open import run ptr
open noderiv

------------------------------------------
-- Length-decreasing rules
------------------------------------------

len-dec-rewrite : Run → maybe (Run × ℕ)
len-dec-rewrite {- Abs-} ((Id "Abs") :: (ParseTree (parsed-posinfo x0)) :: (ParseTree (parsed-binder x1)) :: (ParseTree parsed-ows) :: (ParseTree (parsed-posinfo x2)) :: (ParseTree (parsed-bvar x3)) :: (ParseTree parsed-ows) :: (InputChar ':') :: (ParseTree parsed-ows) :: (ParseTree (parsed-tk x4)) :: (ParseTree parsed-ows) :: (InputChar '.') :: (ParseTree parsed-ows) :: _::_(ParseTree (parsed-type x5)) rest) = just (ParseTree (parsed-type (norm-type (Abs x0 x1 x2 x3 x4 x5))) ::' rest , 14)
len-dec-rewrite {- Abstract-} ((Id "Abstract") :: _::_(InputChar 'θ') rest) = just (ParseTree (parsed-theta (norm-theta Abstract)) ::' rest , 2)
len-dec-rewrite {- AbstractEq-} ((Id "AbstractEq") :: (InputChar 'θ') :: _::_(InputChar '+') rest) = just (ParseTree (parsed-theta (norm-theta AbstractEq)) ::' rest , 3)
len-dec-rewrite {- AbstractVars-} ((Id "AbstractVars") :: (InputChar 'θ') :: (InputChar '<') :: (ParseTree parsed-ows) :: (ParseTree (parsed-vars x0)) :: (ParseTree parsed-ows) :: _::_(InputChar '>') rest) = just (ParseTree (parsed-theta (norm-theta (AbstractVars x0))) ::' rest , 7)
len-dec-rewrite {- All-} ((Id "All") :: _::_(InputChar '∀') rest) = just (ParseTree (parsed-binder (norm-binder All)) ::' rest , 2)
len-dec-rewrite {- App-} ((ParseTree (parsed-aterm x0)) :: (ParseTree parsed-ws) :: (ParseTree (parsed-maybeErased x1)) :: _::_(ParseTree (parsed-aterm x2)) rest) = just (ParseTree (parsed-aterm (norm-term (App x0 x1 x2))) ::' rest , 4)
len-dec-rewrite {- AppTp-} ((ParseTree (parsed-aterm x0)) :: (ParseTree parsed-ws) :: (InputChar '·') :: (ParseTree parsed-ws) :: _::_(ParseTree (parsed-atype x1)) rest) = just (ParseTree (parsed-aterm (norm-term (AppTp x0 x1))) ::' rest , 5)
len-dec-rewrite {- ArgsCons-} ((Id "ArgsCons") :: (ParseTree (parsed-arg x0)) :: _::_(ParseTree (parsed-args x1)) rest) = just (ParseTree (parsed-args (norm-args (ArgsCons x0 x1))) ::' rest , 3)
len-dec-rewrite {- ArgsNil-} ((Id "ArgsNil") :: _::_(ParseTree (parsed-posinfo x0)) rest) = just (ParseTree (parsed-args (norm-args (ArgsNil x0))) ::' rest , 2)
len-dec-rewrite {- Atype-} ((Id "Atype") :: (ParseTree parsed-ows) :: _::_(ParseTree (parsed-atype x0)) rest) = just (ParseTree (parsed-maybeAtype (norm-maybeAtype (Atype x0))) ::' rest , 3)
len-dec-rewrite {- Beta-} ((Id "Beta") :: (ParseTree (parsed-posinfo x0)) :: (InputChar 'β') :: _::_(ParseTree (parsed-optTerm x1)) rest) = just (ParseTree (parsed-lterm (norm-term (Beta x0 x1))) ::' rest , 4)
len-dec-rewrite {- Chi-} ((Id "Chi") :: (ParseTree (parsed-posinfo x0)) :: (InputChar 'χ') :: (ParseTree (parsed-maybeAtype x1)) :: (ParseTree parsed-ows) :: (InputChar '-') :: (ParseTree parsed-ows) :: _::_(ParseTree (parsed-lterm x2)) rest) = just (ParseTree (parsed-lterm (norm-term (Chi x0 x1 x2))) ::' rest , 8)
len-dec-rewrite {- CmdsNext-} ((Id "CmdsNext") :: (ParseTree (parsed-cmd x0)) :: (ParseTree parsed-ws) :: _::_(ParseTree (parsed-cmds x1)) rest) = just (ParseTree (parsed-cmds (norm-cmds (CmdsNext x0 x1))) ::' rest , 4)
len-dec-rewrite {- Decl-} ((Id "Decl") :: (ParseTree (parsed-posinfo x0)) :: (InputChar '(') :: (ParseTree parsed-ows) :: (ParseTree (parsed-posinfo x1)) :: (ParseTree (parsed-bvar x2)) :: (ParseTree parsed-ows) :: (InputChar ':') :: (ParseTree parsed-ows) :: (ParseTree (parsed-tk x3)) :: (ParseTree parsed-ows) :: (InputChar ')') :: _::_(ParseTree (parsed-posinfo x4)) rest) = just (ParseTree (parsed-decl (norm-decl (Decl x0 x1 x2 x3 x4))) ::' rest , 13)
len-dec-rewrite {- DefKind-} ((Id "DefKind") :: (ParseTree (parsed-posinfo x0)) :: (ParseTree (parsed-kvar x1)) :: (ParseTree (parsed-params x2)) :: (ParseTree parsed-ows) :: (InputChar '=') :: (ParseTree parsed-ows) :: (ParseTree (parsed-kind x3)) :: (ParseTree parsed-ows) :: (InputChar '.') :: _::_(ParseTree (parsed-posinfo x4)) rest) = just (ParseTree (parsed-cmd (norm-cmd (DefKind x0 x1 x2 x3 x4))) ::' rest , 11)
len-dec-rewrite {- DefTerm-} ((Id "DefTerm") :: (ParseTree (parsed-posinfo x0)) :: (ParseTree (parsed-var x1)) :: (ParseTree (parsed-maybeCheckType x2)) :: (ParseTree parsed-ows) :: (InputChar '=') :: (ParseTree parsed-ows) :: _::_(ParseTree (parsed-term x3)) rest) = just (ParseTree (parsed-defTermOrType (norm-defTermOrType (DefTerm x0 x1 x2 x3))) ::' rest , 8)
len-dec-rewrite {- DefTermOrType-} ((Id "DefTermOrType") :: (ParseTree (parsed-defTermOrType x0)) :: (ParseTree parsed-ows) :: (InputChar '.') :: _::_(ParseTree (parsed-posinfo x1)) rest) = just (ParseTree (parsed-cmd (norm-cmd (DefTermOrType x0 x1))) ::' rest , 5)
len-dec-rewrite {- DefType-} ((Id "DefType") :: (ParseTree (parsed-posinfo x0)) :: (ParseTree (parsed-var x1)) :: (ParseTree parsed-ows) :: (InputChar '◂') :: (ParseTree parsed-ows) :: (ParseTree (parsed-kind x2)) :: (ParseTree parsed-ows) :: (InputChar '=') :: (ParseTree parsed-ows) :: _::_(ParseTree (parsed-type x3)) rest) = just (ParseTree (parsed-defTermOrType (norm-defTermOrType (DefType x0 x1 x2 x3))) ::' rest , 11)
len-dec-rewrite {- EpsHanf-} ((Id "EpsHanf") :: _::_(InputChar '-') rest) = just (ParseTree (parsed-maybeMinus (norm-maybeMinus EpsHanf)) ::' rest , 2)
len-dec-rewrite {- Epsilon-} ((Id "Epsilon") :: (ParseTree (parsed-posinfo x0)) :: (InputChar 'ε') :: (ParseTree (parsed-leftRight x1)) :: (ParseTree (parsed-maybeMinus x2)) :: (ParseTree parsed-ows) :: _::_(ParseTree (parsed-lterm x3)) rest) = just (ParseTree (parsed-lterm (norm-term (Epsilon x0 x1 x2 x3))) ::' rest , 7)
len-dec-rewrite {- Erased-} ((Id "Erased") :: (InputChar '-') :: _::_(ParseTree parsed-ows) rest) = just (ParseTree (parsed-maybeErased (norm-maybeErased Erased)) ::' rest , 3)
len-dec-rewrite {- ErasedArrow-} ((Id "ErasedArrow") :: _::_(InputChar '➾') rest) = just (ParseTree (parsed-arrowtype (norm-arrowtype ErasedArrow)) ::' rest , 2)
len-dec-rewrite {- ErasedLambda-} ((Id "ErasedLambda") :: _::_(InputChar 'Λ') rest) = just (ParseTree (parsed-lam (norm-lam ErasedLambda)) ::' rest , 2)
len-dec-rewrite {- File-} ((Id "File") :: (ParseTree (parsed-posinfo x0)) :: (ParseTree parsed-ows) :: (ParseTree (parsed-imports x1)) :: (InputChar 'm') :: (InputChar 'o') :: (InputChar 'd') :: (InputChar 'u') :: (InputChar 'l') :: (InputChar 'e') :: (ParseTree parsed-ws) :: (ParseTree (parsed-qvar x2)) :: (ParseTree parsed-ows) :: (ParseTree (parsed-params x3)) :: (ParseTree parsed-ows) :: (InputChar '.') :: (ParseTree parsed-ows) :: (ParseTree (parsed-cmds x4)) :: (ParseTree parsed-ows) :: _::_(ParseTree (parsed-posinfo x5)) rest) = just (ParseTree (parsed-start (norm-start (File x0 x1 x2 x3 x4 x5))) ::' rest , 20)
len-dec-rewrite {- Hole-} ((Id "Hole") :: (ParseTree (parsed-posinfo x0)) :: _::_(InputChar '●') rest) = just (ParseTree (parsed-pterm (norm-term (Hole x0))) ::' rest , 3)
len-dec-rewrite {- Import-} ((Id "Import") :: (ParseTree (parsed-posinfo x0)) :: (InputChar 'i') :: (InputChar 'm') :: (InputChar 'p') :: (InputChar 'o') :: (InputChar 'r') :: (InputChar 't') :: (ParseTree parsed-ws) :: (ParseTree (parsed-fpth x1)) :: (ParseTree (parsed-optAs x2)) :: (ParseTree (parsed-args x3)) :: (ParseTree parsed-ows) :: (InputChar '.') :: _::_(ParseTree (parsed-posinfo x4)) rest) = just (ParseTree (parsed-imprt (norm-imprt (Import x0 x1 x2 x3 x4))) ::' rest , 15)
len-dec-rewrite {- ImportCmd-} ((Id "ImportCmd") :: _::_(ParseTree (parsed-imprt x0)) rest) = just (ParseTree (parsed-cmd (norm-cmd (ImportCmd x0))) ::' rest , 2)
len-dec-rewrite {- ImportsNext-} ((Id "ImportsNext") :: (ParseTree (parsed-imprt x0)) :: (ParseTree parsed-ows) :: _::_(ParseTree (parsed-imports x1)) rest) = just (ParseTree (parsed-imports (norm-imports (ImportsNext x0 x1))) ::' rest , 4)
len-dec-rewrite {- Iota-} ((Id "Iota") :: (ParseTree (parsed-posinfo x0)) :: (InputChar 'ι') :: (ParseTree parsed-ows) :: (ParseTree (parsed-posinfo x1)) :: (ParseTree (parsed-bvar x2)) :: (ParseTree (parsed-optType x3)) :: (ParseTree parsed-ows) :: (InputChar '.') :: (ParseTree parsed-ows) :: _::_(ParseTree (parsed-type x4)) rest) = just (ParseTree (parsed-type (norm-type (Iota x0 x1 x2 x3 x4))) ::' rest , 11)
len-dec-rewrite {- IotaPair-} ((Id "IotaPair") :: (ParseTree (parsed-posinfo x0)) :: (InputChar '[') :: (ParseTree parsed-ows) :: (ParseTree (parsed-term x1)) :: (ParseTree parsed-ows) :: (InputChar ',') :: (ParseTree parsed-ows) :: (ParseTree (parsed-term x2)) :: (ParseTree (parsed-optTerm x3)) :: (ParseTree parsed-ows) :: (InputChar ']') :: _::_(ParseTree (parsed-posinfo x4)) rest) = just (ParseTree (parsed-pterm (norm-term (IotaPair x0 x1 x2 x3 x4))) ::' rest , 13)
len-dec-rewrite {- IotaProj-} ((ParseTree (parsed-pterm x0)) :: (ParseTree parsed-ows) :: (InputChar '.') :: (ParseTree parsed-ows) :: (ParseTree (parsed-num x1)) :: _::_(ParseTree (parsed-posinfo x2)) rest) = just (ParseTree (parsed-pterm (norm-term (IotaProj x0 x1 x2))) ::' rest , 6)
len-dec-rewrite {- KeptLambda-} ((Id "KeptLambda") :: _::_(InputChar 'λ') rest) = just (ParseTree (parsed-lam (norm-lam KeptLambda)) ::' rest , 2)
len-dec-rewrite {- KndArrow-} ((ParseTree (parsed-kind x0)) :: (ParseTree parsed-ows) :: (InputChar '➔') :: (ParseTree parsed-ows) :: _::_(ParseTree (parsed-kind x1)) rest) = just (ParseTree (parsed-kind (norm-kind (KndArrow x0 x1))) ::' rest , 5)
len-dec-rewrite {- KndParens-} ((Id "KndParens") :: (ParseTree (parsed-posinfo x0)) :: (InputChar '(') :: (ParseTree parsed-ows) :: (ParseTree (parsed-kind x1)) :: (ParseTree parsed-ows) :: (InputChar ')') :: _::_(ParseTree (parsed-posinfo x2)) rest) = just (ParseTree (parsed-kind (norm-kind (KndParens x0 x1 x2))) ::' rest , 8)
len-dec-rewrite {- KndPi-} ((Id "KndPi") :: (ParseTree (parsed-posinfo x0)) :: (InputChar 'Π') :: (ParseTree parsed-ows) :: (ParseTree (parsed-posinfo x1)) :: (ParseTree (parsed-bvar x2)) :: (ParseTree parsed-ows) :: (InputChar ':') :: (ParseTree parsed-ows) :: (ParseTree (parsed-tk x3)) :: (ParseTree parsed-ows) :: (InputChar '.') :: (ParseTree parsed-ows) :: _::_(ParseTree (parsed-kind x4)) rest) = just (ParseTree (parsed-kind (norm-kind (KndPi x0 x1 x2 x3 x4))) ::' rest , 14)
len-dec-rewrite {- KndTpArrow-} ((Id "KndTpArrow") :: (ParseTree (parsed-ltype x0)) :: (ParseTree parsed-ows) :: (InputChar '➔') :: (ParseTree parsed-ows) :: _::_(ParseTree (parsed-kind x1)) rest) = just (ParseTree (parsed-kind (norm-kind (KndTpArrow x0 x1))) ::' rest , 6)
len-dec-rewrite {- KndVar-} ((Id "KndVar") :: (ParseTree (parsed-posinfo x0)) :: (ParseTree (parsed-qkvar x1)) :: _::_(ParseTree (parsed-args x2)) rest) = just (ParseTree (parsed-kind (norm-kind (KndVar x0 x1 x2))) ::' rest , 4)
len-dec-rewrite {- Lam-} ((Id "Lam") :: (ParseTree (parsed-posinfo x0)) :: (ParseTree (parsed-lam x1)) :: (ParseTree parsed-ows) :: (ParseTree (parsed-posinfo x2)) :: (ParseTree (parsed-bvar x3)) :: (ParseTree (parsed-optClass x4)) :: (ParseTree parsed-ows) :: (InputChar '.') :: (ParseTree parsed-ows) :: _::_(ParseTree (parsed-term x5)) rest) = just (ParseTree (parsed-term (norm-term (Lam x0 x1 x2 x3 x4 x5))) ::' rest , 11)
len-dec-rewrite {- Left-} ((Id "Left") :: _::_(InputChar 'l') rest) = just (ParseTree (parsed-leftRight (norm-leftRight Left)) ::' rest , 2)
len-dec-rewrite {- Let-} ((Id "Let") :: (ParseTree (parsed-posinfo x0)) :: (InputChar 'l') :: (InputChar 'e') :: (InputChar 't') :: (ParseTree parsed-ws) :: (ParseTree (parsed-defTermOrType x1)) :: (ParseTree parsed-ws) :: (InputChar 'i') :: (InputChar 'n') :: (ParseTree parsed-ws) :: _::_(ParseTree (parsed-term x2)) rest) = just (ParseTree (parsed-term (norm-term (Let x0 x1 x2))) ::' rest , 12)
len-dec-rewrite {- Lft-} ((Id "Lft") :: (ParseTree (parsed-posinfo x0)) :: (InputChar '↑') :: (ParseTree parsed-ows) :: (ParseTree (parsed-posinfo x1)) :: (ParseTree (parsed-var x2)) :: (ParseTree parsed-ows) :: (InputChar '.') :: (ParseTree parsed-ows) :: (ParseTree (parsed-term x3)) :: (ParseTree parsed-ows) :: (InputChar ':') :: (ParseTree parsed-ows) :: _::_(ParseTree (parsed-lliftingType x4)) rest) = just (ParseTree (parsed-ltype (norm-type (Lft x0 x1 x2 x3 x4))) ::' rest , 14)
len-dec-rewrite {- LiftArrow-} ((ParseTree (parsed-liftingType x0)) :: (ParseTree parsed-ows) :: (InputChar '➔') :: (ParseTree parsed-ows) :: _::_(ParseTree (parsed-liftingType x1)) rest) = just (ParseTree (parsed-liftingType (norm-liftingType (LiftArrow x0 x1))) ::' rest , 5)
len-dec-rewrite {- LiftParens-} ((Id "LiftParens") :: (ParseTree (parsed-posinfo x0)) :: (InputChar '(') :: (ParseTree parsed-ows) :: (ParseTree (parsed-liftingType x1)) :: (ParseTree parsed-ows) :: (InputChar ')') :: _::_(ParseTree (parsed-posinfo x2)) rest) = just (ParseTree (parsed-lliftingType (norm-liftingType (LiftParens x0 x1 x2))) ::' rest , 8)
len-dec-rewrite {- LiftPi-} ((Id "LiftPi") :: (ParseTree (parsed-posinfo x0)) :: (InputChar 'Π') :: (ParseTree parsed-ows) :: (ParseTree (parsed-bvar x1)) :: (ParseTree parsed-ows) :: (InputChar ':') :: (ParseTree parsed-ows) :: (ParseTree (parsed-type x2)) :: (ParseTree parsed-ows) :: (InputChar '.') :: (ParseTree parsed-ows) :: _::_(ParseTree (parsed-liftingType x3)) rest) = just (ParseTree (parsed-liftingType (norm-liftingType (LiftPi x0 x1 x2 x3))) ::' rest , 13)
len-dec-rewrite {- LiftStar-} ((Id "LiftStar") :: (ParseTree (parsed-posinfo x0)) :: _::_(InputChar '☆') rest) = just (ParseTree (parsed-lliftingType (norm-liftingType (LiftStar x0))) ::' rest , 3)
len-dec-rewrite {- LiftTpArrow-} ((Id "LiftTpArrow") :: (ParseTree (parsed-type x0)) :: (ParseTree parsed-ows) :: (InputChar '➔') :: (ParseTree parsed-ows) :: _::_(ParseTree (parsed-liftingType x1)) rest) = just (ParseTree (parsed-liftingType (norm-liftingType (LiftTpArrow x0 x1))) ::' rest , 6)
len-dec-rewrite {- LtermsCons-} ((Id "LtermsCons") :: (ParseTree parsed-ws) :: (ParseTree (parsed-maybeErased x0)) :: (ParseTree (parsed-lterm x1)) :: _::_(ParseTree (parsed-lterms x2)) rest) = just (ParseTree (parsed-lterms (norm-lterms (LtermsCons x0 x1 x2))) ::' rest , 5)
len-dec-rewrite {- LtermsNil-} ((Id "LtermsNil") :: _::_(ParseTree (parsed-posinfo x0)) rest) = just (ParseTree (parsed-lterms (norm-lterms (LtermsNil x0))) ::' rest , 2)
len-dec-rewrite {- NoSpans-} ((Id "NoSpans") :: (InputChar '{') :: (InputChar '^') :: (ParseTree (parsed-type x0)) :: (ParseTree (parsed-posinfo x1)) :: (InputChar '^') :: _::_(InputChar '}') rest) = just (ParseTree (parsed-type (norm-type (NoSpans x0 x1))) ::' rest , 7)
len-dec-rewrite {- P0-} ((Id "P0") :: _::_(InputChar 'a') rest) = just (ParseTree (parsed-alpha-range-1 (string-append 0 (char-to-string 'a'))) ::' rest , 2)
len-dec-rewrite {- P1-} ((Id "P1") :: _::_(InputChar 'b') rest) = just (ParseTree (parsed-alpha-range-1 (string-append 0 (char-to-string 'b'))) ::' rest , 2)
len-dec-rewrite {- P10-} ((Id "P10") :: _::_(InputChar 'k') rest) = just (ParseTree (parsed-alpha-range-1 (string-append 0 (char-to-string 'k'))) ::' rest , 2)
len-dec-rewrite {- P100-} ((Id "P100") :: (ParseTree (parsed-fpth-bar-15 x0)) :: _::_(ParseTree (parsed-fpth-star-18 x1)) rest) = just (ParseTree (parsed-fpth (string-append 1 x0 x1)) ::' rest , 3)
len-dec-rewrite {- P101-} ((Id "P101") :: _::_(ParseTree (parsed-kvar x0)) rest) = just (ParseTree (parsed-qkvar (string-append 0 x0)) ::' rest , 2)
len-dec-rewrite {- P102-} ((Id "P102") :: (ParseTree (parsed-var x0)) :: (InputChar '.') :: _::_(ParseTree (parsed-qkvar x1)) rest) = just (ParseTree (parsed-qkvar (string-append 2 x0 (char-to-string '.') x1)) ::' rest , 4)
len-dec-rewrite {- P103-} ((Id "P103") :: _::_(ParseTree (parsed-alpha x0)) rest) = just (ParseTree (parsed-kvar-bar-19 (string-append 0 x0)) ::' rest , 2)
len-dec-rewrite {- P104-} ((Id "P104") :: _::_(ParseTree (parsed-numpunct x0)) rest) = just (ParseTree (parsed-kvar-bar-19 (string-append 0 x0)) ::' rest , 2)
len-dec-rewrite {- P106-} ((Id "P106") :: (ParseTree (parsed-kvar-bar-19 x0)) :: _::_(ParseTree (parsed-kvar-star-20 x1)) rest) = just (ParseTree (parsed-kvar-star-20 (string-append 1 x0 x1)) ::' rest , 3)
len-dec-rewrite {- P107-} ((Id "P107") :: (InputChar '𝒌') :: _::_(ParseTree (parsed-kvar-star-20 x0)) rest) = just (ParseTree (parsed-kvar (string-append 1 (char-to-string '𝒌') x0)) ::' rest , 3)
len-dec-rewrite {- P108-} ((Id "P108") :: _::_(InputChar '◂') rest) = just (ParseTree parsed-otherpunct-bar-21 ::' rest , 2)
len-dec-rewrite {- P109-} ((Id "P109") :: _::_(InputChar 'ω') rest) = just (ParseTree parsed-otherpunct-bar-21 ::' rest , 2)
len-dec-rewrite {- P11-} ((Id "P11") :: _::_(InputChar 'l') rest) = just (ParseTree (parsed-alpha-range-1 (string-append 0 (char-to-string 'l'))) ::' rest , 2)
len-dec-rewrite {- P110-} ((Id "P110") :: _::_(InputChar 'φ') rest) = just (ParseTree parsed-otherpunct-bar-22 ::' rest , 2)
len-dec-rewrite {- P111-} ((Id "P111") :: _::_(ParseTree parsed-otherpunct-bar-21) rest) = just (ParseTree parsed-otherpunct-bar-22 ::' rest , 2)
len-dec-rewrite {- P112-} ((Id "P112") :: _::_(InputChar 'υ') rest) = just (ParseTree parsed-otherpunct-bar-23 ::' rest , 2)
len-dec-rewrite {- P113-} ((Id "P113") :: _::_(ParseTree parsed-otherpunct-bar-22) rest) = just (ParseTree parsed-otherpunct-bar-23 ::' rest , 2)
len-dec-rewrite {- P114-} ((Id "P114") :: _::_(InputChar 'μ') rest) = just (ParseTree parsed-otherpunct-bar-24 ::' rest , 2)
len-dec-rewrite {- P115-} ((Id "P115") :: _::_(ParseTree parsed-otherpunct-bar-23) rest) = just (ParseTree parsed-otherpunct-bar-24 ::' rest , 2)
len-dec-rewrite {- P116-} ((Id "P116") :: _::_(InputChar 'χ') rest) = just (ParseTree parsed-otherpunct-bar-25 ::' rest , 2)
len-dec-rewrite {- P117-} ((Id "P117") :: _::_(ParseTree parsed-otherpunct-bar-24) rest) = just (ParseTree parsed-otherpunct-bar-25 ::' rest , 2)
len-dec-rewrite {- P118-} ((Id "P118") :: _::_(InputChar 'δ') rest) = just (ParseTree parsed-otherpunct-bar-26 ::' rest , 2)
len-dec-rewrite {- P119-} ((Id "P119") :: _::_(ParseTree parsed-otherpunct-bar-25) rest) = just (ParseTree parsed-otherpunct-bar-26 ::' rest , 2)
len-dec-rewrite {- P12-} ((Id "P12") :: _::_(InputChar 'm') rest) = just (ParseTree (parsed-alpha-range-1 (string-append 0 (char-to-string 'm'))) ::' rest , 2)
len-dec-rewrite {- P120-} ((Id "P120") :: _::_(InputChar '\"') rest) = just (ParseTree parsed-otherpunct-bar-27 ::' rest , 2)
len-dec-rewrite {- P121-} ((Id "P121") :: _::_(ParseTree parsed-otherpunct-bar-26) rest) = just (ParseTree parsed-otherpunct-bar-27 ::' rest , 2)
len-dec-rewrite {- P122-} ((Id "P122") :: _::_(InputChar '≃') rest) = just (ParseTree parsed-otherpunct-bar-28 ::' rest , 2)
len-dec-rewrite {- P123-} ((Id "P123") :: _::_(ParseTree parsed-otherpunct-bar-27) rest) = just (ParseTree parsed-otherpunct-bar-28 ::' rest , 2)
len-dec-rewrite {- P124-} ((Id "P124") :: _::_(InputChar '>') rest) = just (ParseTree parsed-otherpunct-bar-29 ::' rest , 2)
len-dec-rewrite {- P125-} ((Id "P125") :: _::_(ParseTree parsed-otherpunct-bar-28) rest) = just (ParseTree parsed-otherpunct-bar-29 ::' rest , 2)
len-dec-rewrite {- P126-} ((Id "P126") :: _::_(InputChar '<') rest) = just (ParseTree parsed-otherpunct-bar-30 ::' rest , 2)
len-dec-rewrite {- P127-} ((Id "P127") :: _::_(ParseTree parsed-otherpunct-bar-29) rest) = just (ParseTree parsed-otherpunct-bar-30 ::' rest , 2)
len-dec-rewrite {- P128-} ((Id "P128") :: _::_(InputChar '+') rest) = just (ParseTree parsed-otherpunct-bar-31 ::' rest , 2)
len-dec-rewrite {- P129-} ((Id "P129") :: _::_(ParseTree parsed-otherpunct-bar-30) rest) = just (ParseTree parsed-otherpunct-bar-31 ::' rest , 2)
len-dec-rewrite {- P13-} ((Id "P13") :: _::_(InputChar 'n') rest) = just (ParseTree (parsed-alpha-range-1 (string-append 0 (char-to-string 'n'))) ::' rest , 2)
len-dec-rewrite {- P130-} ((Id "P130") :: _::_(InputChar 'θ') rest) = just (ParseTree parsed-otherpunct-bar-32 ::' rest , 2)
len-dec-rewrite {- P131-} ((Id "P131") :: _::_(ParseTree parsed-otherpunct-bar-31) rest) = just (ParseTree parsed-otherpunct-bar-32 ::' rest , 2)
len-dec-rewrite {- P132-} ((Id "P132") :: _::_(InputChar 'ς') rest) = just (ParseTree parsed-otherpunct-bar-33 ::' rest , 2)
len-dec-rewrite {- P133-} ((Id "P133") :: _::_(ParseTree parsed-otherpunct-bar-32) rest) = just (ParseTree parsed-otherpunct-bar-33 ::' rest , 2)
len-dec-rewrite {- P134-} ((Id "P134") :: _::_(InputChar '=') rest) = just (ParseTree parsed-otherpunct-bar-34 ::' rest , 2)
len-dec-rewrite {- P135-} ((Id "P135") :: _::_(ParseTree parsed-otherpunct-bar-33) rest) = just (ParseTree parsed-otherpunct-bar-34 ::' rest , 2)
len-dec-rewrite {- P136-} ((Id "P136") :: _::_(InputChar '𝒌') rest) = just (ParseTree parsed-otherpunct-bar-35 ::' rest , 2)
len-dec-rewrite {- P137-} ((Id "P137") :: _::_(ParseTree parsed-otherpunct-bar-34) rest) = just (ParseTree parsed-otherpunct-bar-35 ::' rest , 2)
len-dec-rewrite {- P138-} ((Id "P138") :: _::_(InputChar '-') rest) = just (ParseTree parsed-otherpunct-bar-36 ::' rest , 2)
len-dec-rewrite {- P139-} ((Id "P139") :: _::_(ParseTree parsed-otherpunct-bar-35) rest) = just (ParseTree parsed-otherpunct-bar-36 ::' rest , 2)
len-dec-rewrite {- P14-} ((Id "P14") :: _::_(InputChar 'o') rest) = just (ParseTree (parsed-alpha-range-1 (string-append 0 (char-to-string 'o'))) ::' rest , 2)
len-dec-rewrite {- P140-} ((Id "P140") :: _::_(InputChar 'β') rest) = just (ParseTree parsed-otherpunct-bar-37 ::' rest , 2)
len-dec-rewrite {- P141-} ((Id "P141") :: _::_(ParseTree parsed-otherpunct-bar-36) rest) = just (ParseTree parsed-otherpunct-bar-37 ::' rest , 2)
len-dec-rewrite {- P142-} ((Id "P142") :: _::_(InputChar 'ε') rest) = just (ParseTree parsed-otherpunct-bar-38 ::' rest , 2)
len-dec-rewrite {- P143-} ((Id "P143") :: _::_(ParseTree parsed-otherpunct-bar-37) rest) = just (ParseTree parsed-otherpunct-bar-38 ::' rest , 2)
len-dec-rewrite {- P144-} ((Id "P144") :: _::_(InputChar 'ρ') rest) = just (ParseTree parsed-otherpunct-bar-39 ::' rest , 2)
len-dec-rewrite {- P145-} ((Id "P145") :: _::_(ParseTree parsed-otherpunct-bar-38) rest) = just (ParseTree parsed-otherpunct-bar-39 ::' rest , 2)
len-dec-rewrite {- P146-} ((Id "P146") :: _::_(InputChar 'Λ') rest) = just (ParseTree parsed-otherpunct-bar-40 ::' rest , 2)
len-dec-rewrite {- P147-} ((Id "P147") :: _::_(ParseTree parsed-otherpunct-bar-39) rest) = just (ParseTree parsed-otherpunct-bar-40 ::' rest , 2)
len-dec-rewrite {- P148-} ((Id "P148") :: _::_(InputChar '?') rest) = just (ParseTree parsed-otherpunct-bar-41 ::' rest , 2)
len-dec-rewrite {- P149-} ((Id "P149") :: _::_(ParseTree parsed-otherpunct-bar-40) rest) = just (ParseTree parsed-otherpunct-bar-41 ::' rest , 2)
len-dec-rewrite {- P15-} ((Id "P15") :: _::_(InputChar 'p') rest) = just (ParseTree (parsed-alpha-range-1 (string-append 0 (char-to-string 'p'))) ::' rest , 2)
len-dec-rewrite {- P150-} ((Id "P150") :: _::_(InputChar '⇒') rest) = just (ParseTree parsed-otherpunct-bar-42 ::' rest , 2)
len-dec-rewrite {- P151-} ((Id "P151") :: _::_(ParseTree parsed-otherpunct-bar-41) rest) = just (ParseTree parsed-otherpunct-bar-42 ::' rest , 2)
len-dec-rewrite {- P152-} ((Id "P152") :: _::_(InputChar '}') rest) = just (ParseTree parsed-otherpunct-bar-43 ::' rest , 2)
len-dec-rewrite {- P153-} ((Id "P153") :: _::_(ParseTree parsed-otherpunct-bar-42) rest) = just (ParseTree parsed-otherpunct-bar-43 ::' rest , 2)
len-dec-rewrite {- P154-} ((Id "P154") :: _::_(InputChar '{') rest) = just (ParseTree parsed-otherpunct-bar-44 ::' rest , 2)
len-dec-rewrite {- P155-} ((Id "P155") :: _::_(ParseTree parsed-otherpunct-bar-43) rest) = just (ParseTree parsed-otherpunct-bar-44 ::' rest , 2)
len-dec-rewrite {- P156-} ((Id "P156") :: _::_(InputChar '!') rest) = just (ParseTree parsed-otherpunct-bar-45 ::' rest , 2)
len-dec-rewrite {- P157-} ((Id "P157") :: _::_(ParseTree parsed-otherpunct-bar-44) rest) = just (ParseTree parsed-otherpunct-bar-45 ::' rest , 2)
len-dec-rewrite {- P158-} ((Id "P158") :: _::_(InputChar ',') rest) = just (ParseTree parsed-otherpunct-bar-46 ::' rest , 2)
len-dec-rewrite {- P159-} ((Id "P159") :: _::_(ParseTree parsed-otherpunct-bar-45) rest) = just (ParseTree parsed-otherpunct-bar-46 ::' rest , 2)
len-dec-rewrite {- P16-} ((Id "P16") :: _::_(InputChar 'q') rest) = just (ParseTree (parsed-alpha-range-1 (string-append 0 (char-to-string 'q'))) ::' rest , 2)
len-dec-rewrite {- P160-} ((Id "P160") :: _::_(InputChar ']') rest) = just (ParseTree parsed-otherpunct-bar-47 ::' rest , 2)
len-dec-rewrite {- P161-} ((Id "P161") :: _::_(ParseTree parsed-otherpunct-bar-46) rest) = just (ParseTree parsed-otherpunct-bar-47 ::' rest , 2)
len-dec-rewrite {- P162-} ((Id "P162") :: _::_(InputChar '[') rest) = just (ParseTree parsed-otherpunct-bar-48 ::' rest , 2)
len-dec-rewrite {- P163-} ((Id "P163") :: _::_(ParseTree parsed-otherpunct-bar-47) rest) = just (ParseTree parsed-otherpunct-bar-48 ::' rest , 2)
len-dec-rewrite {- P164-} ((Id "P164") :: _::_(InputChar '.') rest) = just (ParseTree parsed-otherpunct-bar-49 ::' rest , 2)
len-dec-rewrite {- P165-} ((Id "P165") :: _::_(ParseTree parsed-otherpunct-bar-48) rest) = just (ParseTree parsed-otherpunct-bar-49 ::' rest , 2)
len-dec-rewrite {- P166-} ((Id "P166") :: _::_(InputChar ':') rest) = just (ParseTree parsed-otherpunct-bar-50 ::' rest , 2)
len-dec-rewrite {- P167-} ((Id "P167") :: _::_(ParseTree parsed-otherpunct-bar-49) rest) = just (ParseTree parsed-otherpunct-bar-50 ::' rest , 2)
len-dec-rewrite {- P168-} ((Id "P168") :: _::_(InputChar ')') rest) = just (ParseTree parsed-otherpunct-bar-51 ::' rest , 2)
len-dec-rewrite {- P169-} ((Id "P169") :: _::_(ParseTree parsed-otherpunct-bar-50) rest) = just (ParseTree parsed-otherpunct-bar-51 ::' rest , 2)
len-dec-rewrite {- P17-} ((Id "P17") :: _::_(InputChar 'r') rest) = just (ParseTree (parsed-alpha-range-1 (string-append 0 (char-to-string 'r'))) ::' rest , 2)
len-dec-rewrite {- P170-} ((Id "P170") :: _::_(InputChar '(') rest) = just (ParseTree parsed-otherpunct-bar-52 ::' rest , 2)
len-dec-rewrite {- P171-} ((Id "P171") :: _::_(ParseTree parsed-otherpunct-bar-51) rest) = just (ParseTree parsed-otherpunct-bar-52 ::' rest , 2)
len-dec-rewrite {- P172-} ((Id "P172") :: _::_(InputChar '●') rest) = just (ParseTree parsed-otherpunct-bar-53 ::' rest , 2)
len-dec-rewrite {- P173-} ((Id "P173") :: _::_(ParseTree parsed-otherpunct-bar-52) rest) = just (ParseTree parsed-otherpunct-bar-53 ::' rest , 2)
len-dec-rewrite {- P174-} ((Id "P174") :: _::_(InputChar '↑') rest) = just (ParseTree parsed-otherpunct-bar-54 ::' rest , 2)
len-dec-rewrite {- P175-} ((Id "P175") :: _::_(ParseTree parsed-otherpunct-bar-53) rest) = just (ParseTree parsed-otherpunct-bar-54 ::' rest , 2)
len-dec-rewrite {- P176-} ((Id "P176") :: _::_(InputChar '➾') rest) = just (ParseTree parsed-otherpunct-bar-55 ::' rest , 2)
len-dec-rewrite {- P177-} ((Id "P177") :: _::_(ParseTree parsed-otherpunct-bar-54) rest) = just (ParseTree parsed-otherpunct-bar-55 ::' rest , 2)
len-dec-rewrite {- P178-} ((Id "P178") :: _::_(InputChar '➔') rest) = just (ParseTree parsed-otherpunct-bar-56 ::' rest , 2)
len-dec-rewrite {- P179-} ((Id "P179") :: _::_(ParseTree parsed-otherpunct-bar-55) rest) = just (ParseTree parsed-otherpunct-bar-56 ::' rest , 2)
len-dec-rewrite {- P18-} ((Id "P18") :: _::_(InputChar 's') rest) = just (ParseTree (parsed-alpha-range-1 (string-append 0 (char-to-string 's'))) ::' rest , 2)
len-dec-rewrite {- P180-} ((Id "P180") :: _::_(InputChar '⇐') rest) = just (ParseTree parsed-otherpunct-bar-57 ::' rest , 2)
len-dec-rewrite {- P181-} ((Id "P181") :: _::_(ParseTree parsed-otherpunct-bar-56) rest) = just (ParseTree parsed-otherpunct-bar-57 ::' rest , 2)
len-dec-rewrite {- P182-} ((Id "P182") :: _::_(InputChar '·') rest) = just (ParseTree parsed-otherpunct-bar-58 ::' rest , 2)
len-dec-rewrite {- P183-} ((Id "P183") :: _::_(ParseTree parsed-otherpunct-bar-57) rest) = just (ParseTree parsed-otherpunct-bar-58 ::' rest , 2)
len-dec-rewrite {- P184-} ((Id "P184") :: _::_(InputChar '☆') rest) = just (ParseTree parsed-otherpunct-bar-59 ::' rest , 2)
len-dec-rewrite {- P185-} ((Id "P185") :: _::_(ParseTree parsed-otherpunct-bar-58) rest) = just (ParseTree parsed-otherpunct-bar-59 ::' rest , 2)
len-dec-rewrite {- P186-} ((Id "P186") :: _::_(InputChar '★') rest) = just (ParseTree parsed-otherpunct-bar-60 ::' rest , 2)
len-dec-rewrite {- P187-} ((Id "P187") :: _::_(ParseTree parsed-otherpunct-bar-59) rest) = just (ParseTree parsed-otherpunct-bar-60 ::' rest , 2)
len-dec-rewrite {- P188-} ((Id "P188") :: _::_(InputChar 'π') rest) = just (ParseTree parsed-otherpunct-bar-61 ::' rest , 2)
len-dec-rewrite {- P189-} ((Id "P189") :: _::_(ParseTree parsed-otherpunct-bar-60) rest) = just (ParseTree parsed-otherpunct-bar-61 ::' rest , 2)
len-dec-rewrite {- P19-} ((Id "P19") :: _::_(InputChar 't') rest) = just (ParseTree (parsed-alpha-range-1 (string-append 0 (char-to-string 't'))) ::' rest , 2)
len-dec-rewrite {- P190-} ((Id "P190") :: _::_(InputChar '∀') rest) = just (ParseTree parsed-otherpunct-bar-62 ::' rest , 2)
len-dec-rewrite {- P191-} ((Id "P191") :: _::_(ParseTree parsed-otherpunct-bar-61) rest) = just (ParseTree parsed-otherpunct-bar-62 ::' rest , 2)
len-dec-rewrite {- P192-} ((Id "P192") :: _::_(InputChar 'λ') rest) = just (ParseTree parsed-otherpunct-bar-63 ::' rest , 2)
len-dec-rewrite {- P193-} ((Id "P193") :: _::_(ParseTree parsed-otherpunct-bar-62) rest) = just (ParseTree parsed-otherpunct-bar-63 ::' rest , 2)
len-dec-rewrite {- P194-} ((Id "P194") :: _::_(InputChar 'ι') rest) = just (ParseTree parsed-otherpunct-bar-64 ::' rest , 2)
len-dec-rewrite {- P195-} ((Id "P195") :: _::_(ParseTree parsed-otherpunct-bar-63) rest) = just (ParseTree parsed-otherpunct-bar-64 ::' rest , 2)
len-dec-rewrite {- P196-} ((Id "P196") :: _::_(InputChar 'Π') rest) = just (ParseTree parsed-otherpunct-bar-65 ::' rest , 2)
len-dec-rewrite {- P197-} ((Id "P197") :: _::_(ParseTree parsed-otherpunct-bar-64) rest) = just (ParseTree parsed-otherpunct-bar-65 ::' rest , 2)
len-dec-rewrite {- P198-} ((Id "P198") :: _::_(InputChar '□') rest) = just (ParseTree parsed-otherpunct-bar-66 ::' rest , 2)
len-dec-rewrite {- P199-} ((Id "P199") :: _::_(ParseTree parsed-otherpunct-bar-65) rest) = just (ParseTree parsed-otherpunct-bar-66 ::' rest , 2)
len-dec-rewrite {- P2-} ((Id "P2") :: _::_(InputChar 'c') rest) = just (ParseTree (parsed-alpha-range-1 (string-append 0 (char-to-string 'c'))) ::' rest , 2)
len-dec-rewrite {- P20-} ((Id "P20") :: _::_(InputChar 'u') rest) = just (ParseTree (parsed-alpha-range-1 (string-append 0 (char-to-string 'u'))) ::' rest , 2)
len-dec-rewrite {- P200-} ((Id "P200") :: _::_(InputChar '|') rest) = just (ParseTree parsed-otherpunct-bar-67 ::' rest , 2)
len-dec-rewrite {- P201-} ((Id "P201") :: _::_(ParseTree parsed-otherpunct-bar-66) rest) = just (ParseTree parsed-otherpunct-bar-67 ::' rest , 2)
len-dec-rewrite {- P202-} ((Id "P202") :: _::_(ParseTree parsed-otherpunct-bar-67) rest) = just (ParseTree parsed-otherpunct ::' rest , 2)
len-dec-rewrite {- P203-} ((Id "P203") :: _::_(InputChar '%') rest) = just (ParseTree parsed-anychar-bar-68 ::' rest , 2)
len-dec-rewrite {- P204-} ((Id "P204") :: _::_(ParseTree parsed-otherpunct) rest) = just (ParseTree parsed-anychar-bar-68 ::' rest , 2)
len-dec-rewrite {- P205-} ((Id "P205") :: _::_(InputChar ' ') rest) = just (ParseTree parsed-anychar-bar-69 ::' rest , 2)
len-dec-rewrite {- P206-} ((Id "P206") :: _::_(ParseTree parsed-anychar-bar-68) rest) = just (ParseTree parsed-anychar-bar-69 ::' rest , 2)
len-dec-rewrite {- P207-} ((Id "P207") :: _::_(InputChar '\t') rest) = just (ParseTree parsed-anychar-bar-70 ::' rest , 2)
len-dec-rewrite {- P208-} ((Id "P208") :: _::_(ParseTree parsed-anychar-bar-69) rest) = just (ParseTree parsed-anychar-bar-70 ::' rest , 2)
len-dec-rewrite {- P209-} ((Id "P209") :: _::_(ParseTree (parsed-numpunct x0)) rest) = just (ParseTree parsed-anychar-bar-71 ::' rest , 2)
len-dec-rewrite {- P21-} ((Id "P21") :: _::_(InputChar 'v') rest) = just (ParseTree (parsed-alpha-range-1 (string-append 0 (char-to-string 'v'))) ::' rest , 2)
len-dec-rewrite {- P210-} ((Id "P210") :: _::_(ParseTree parsed-anychar-bar-70) rest) = just (ParseTree parsed-anychar-bar-71 ::' rest , 2)
len-dec-rewrite {- P211-} ((Id "P211") :: _::_(ParseTree (parsed-alpha x0)) rest) = just (ParseTree parsed-anychar-bar-72 ::' rest , 2)
len-dec-rewrite {- P212-} ((Id "P212") :: _::_(ParseTree parsed-anychar-bar-71) rest) = just (ParseTree parsed-anychar-bar-72 ::' rest , 2)
len-dec-rewrite {- P213-} ((Id "P213") :: _::_(ParseTree parsed-anychar-bar-72) rest) = just (ParseTree parsed-anychar ::' rest , 2)
len-dec-rewrite {- P215-} ((Id "P215") :: (ParseTree parsed-anychar) :: _::_(ParseTree parsed-comment-star-73) rest) = just (ParseTree parsed-comment-star-73 ::' rest , 3)
len-dec-rewrite {- P216-} ((Id "P216") :: (InputChar '%') :: (ParseTree parsed-comment-star-73) :: _::_(InputChar '\n') rest) = just (ParseTree parsed-comment ::' rest , 4)
len-dec-rewrite {- P217-} ((Id "P217") :: _::_(InputChar ' ') rest) = just (ParseTree parsed-aws-bar-74 ::' rest , 2)
len-dec-rewrite {- P218-} ((Id "P218") :: _::_(ParseTree parsed-comment) rest) = just (ParseTree parsed-aws-bar-74 ::' rest , 2)
len-dec-rewrite {- P219-} ((Id "P219") :: _::_(InputChar '\t') rest) = just (ParseTree parsed-aws-bar-75 ::' rest , 2)
len-dec-rewrite {- P22-} ((Id "P22") :: _::_(InputChar 'w') rest) = just (ParseTree (parsed-alpha-range-1 (string-append 0 (char-to-string 'w'))) ::' rest , 2)
len-dec-rewrite {- P220-} ((Id "P220") :: _::_(ParseTree parsed-aws-bar-74) rest) = just (ParseTree parsed-aws-bar-75 ::' rest , 2)
len-dec-rewrite {- P221-} ((Id "P221") :: _::_(InputChar '\n') rest) = just (ParseTree parsed-aws-bar-76 ::' rest , 2)
len-dec-rewrite {- P222-} ((Id "P222") :: _::_(ParseTree parsed-aws-bar-75) rest) = just (ParseTree parsed-aws-bar-76 ::' rest , 2)
len-dec-rewrite {- P223-} ((Id "P223") :: _::_(ParseTree parsed-aws-bar-76) rest) = just (ParseTree parsed-aws ::' rest , 2)
len-dec-rewrite {- P224-} ((Id "P224") :: _::_(ParseTree parsed-aws) rest) = just (ParseTree parsed-ws-plus-77 ::' rest , 2)
len-dec-rewrite {- P225-} ((Id "P225") :: (ParseTree parsed-aws) :: _::_(ParseTree parsed-ws-plus-77) rest) = just (ParseTree parsed-ws-plus-77 ::' rest , 3)
len-dec-rewrite {- P226-} ((Id "P226") :: _::_(ParseTree parsed-ws-plus-77) rest) = just (ParseTree parsed-ws ::' rest , 2)
len-dec-rewrite {- P228-} ((Id "P228") :: (ParseTree parsed-aws) :: _::_(ParseTree parsed-ows-star-78) rest) = just (ParseTree parsed-ows-star-78 ::' rest , 3)
len-dec-rewrite {- P229-} ((Id "P229") :: _::_(ParseTree parsed-ows-star-78) rest) = just (ParseTree parsed-ows ::' rest , 2)
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
len-dec-rewrite {- P55-} ((Id "P55") :: _::_(InputChar '0') rest) = just (ParseTree (parsed-numone-range-4 (string-append 0 (char-to-string '0'))) ::' rest , 2)
len-dec-rewrite {- P56-} ((Id "P56") :: _::_(InputChar '1') rest) = just (ParseTree (parsed-numone-range-4 (string-append 0 (char-to-string '1'))) ::' rest , 2)
len-dec-rewrite {- P57-} ((Id "P57") :: _::_(InputChar '2') rest) = just (ParseTree (parsed-numone-range-4 (string-append 0 (char-to-string '2'))) ::' rest , 2)
len-dec-rewrite {- P58-} ((Id "P58") :: _::_(InputChar '3') rest) = just (ParseTree (parsed-numone-range-4 (string-append 0 (char-to-string '3'))) ::' rest , 2)
len-dec-rewrite {- P59-} ((Id "P59") :: _::_(InputChar '4') rest) = just (ParseTree (parsed-numone-range-4 (string-append 0 (char-to-string '4'))) ::' rest , 2)
len-dec-rewrite {- P6-} ((Id "P6") :: _::_(InputChar 'g') rest) = just (ParseTree (parsed-alpha-range-1 (string-append 0 (char-to-string 'g'))) ::' rest , 2)
len-dec-rewrite {- P60-} ((Id "P60") :: _::_(InputChar '5') rest) = just (ParseTree (parsed-numone-range-4 (string-append 0 (char-to-string '5'))) ::' rest , 2)
len-dec-rewrite {- P61-} ((Id "P61") :: _::_(InputChar '6') rest) = just (ParseTree (parsed-numone-range-4 (string-append 0 (char-to-string '6'))) ::' rest , 2)
len-dec-rewrite {- P62-} ((Id "P62") :: _::_(InputChar '7') rest) = just (ParseTree (parsed-numone-range-4 (string-append 0 (char-to-string '7'))) ::' rest , 2)
len-dec-rewrite {- P63-} ((Id "P63") :: _::_(InputChar '8') rest) = just (ParseTree (parsed-numone-range-4 (string-append 0 (char-to-string '8'))) ::' rest , 2)
len-dec-rewrite {- P64-} ((Id "P64") :: _::_(InputChar '9') rest) = just (ParseTree (parsed-numone-range-4 (string-append 0 (char-to-string '9'))) ::' rest , 2)
len-dec-rewrite {- P65-} ((Id "P65") :: _::_(ParseTree (parsed-numone-range-4 x0)) rest) = just (ParseTree (parsed-numone (string-append 0 x0)) ::' rest , 2)
len-dec-rewrite {- P66-} ((Id "P66") :: _::_(ParseTree (parsed-numone x0)) rest) = just (ParseTree (parsed-num-plus-5 (string-append 0 x0)) ::' rest , 2)
len-dec-rewrite {- P67-} ((Id "P67") :: (ParseTree (parsed-numone x0)) :: _::_(ParseTree (parsed-num-plus-5 x1)) rest) = just (ParseTree (parsed-num-plus-5 (string-append 1 x0 x1)) ::' rest , 3)
len-dec-rewrite {- P68-} ((Id "P68") :: _::_(ParseTree (parsed-num-plus-5 x0)) rest) = just (ParseTree (parsed-num (string-append 0 x0)) ::' rest , 2)
len-dec-rewrite {- P69-} ((Id "P69") :: _::_(InputChar '#') rest) = just (ParseTree (parsed-numpunct-bar-6 (string-append 0 (char-to-string '#'))) ::' rest , 2)
len-dec-rewrite {- P7-} ((Id "P7") :: _::_(InputChar 'h') rest) = just (ParseTree (parsed-alpha-range-1 (string-append 0 (char-to-string 'h'))) ::' rest , 2)
len-dec-rewrite {- P70-} ((Id "P70") :: _::_(InputChar '_') rest) = just (ParseTree (parsed-numpunct-bar-6 (string-append 0 (char-to-string '_'))) ::' rest , 2)
len-dec-rewrite {- P71-} ((Id "P71") :: _::_(InputChar '~') rest) = just (ParseTree (parsed-numpunct-bar-7 (string-append 0 (char-to-string '~'))) ::' rest , 2)
len-dec-rewrite {- P72-} ((Id "P72") :: _::_(ParseTree (parsed-numpunct-bar-6 x0)) rest) = just (ParseTree (parsed-numpunct-bar-7 (string-append 0 x0)) ::' rest , 2)
len-dec-rewrite {- P73-} ((Id "P73") :: _::_(InputChar '-') rest) = just (ParseTree (parsed-numpunct-bar-8 (string-append 0 (char-to-string '-'))) ::' rest , 2)
len-dec-rewrite {- P74-} ((Id "P74") :: _::_(ParseTree (parsed-numpunct-bar-7 x0)) rest) = just (ParseTree (parsed-numpunct-bar-8 (string-append 0 x0)) ::' rest , 2)
len-dec-rewrite {- P75-} ((Id "P75") :: _::_(InputChar '\'') rest) = just (ParseTree (parsed-numpunct-bar-9 (string-append 0 (char-to-string '\''))) ::' rest , 2)
len-dec-rewrite {- P76-} ((Id "P76") :: _::_(ParseTree (parsed-numpunct-bar-8 x0)) rest) = just (ParseTree (parsed-numpunct-bar-9 (string-append 0 x0)) ::' rest , 2)
len-dec-rewrite {- P77-} ((Id "P77") :: _::_(ParseTree (parsed-numone x0)) rest) = just (ParseTree (parsed-numpunct-bar-10 (string-append 0 x0)) ::' rest , 2)
len-dec-rewrite {- P78-} ((Id "P78") :: _::_(ParseTree (parsed-numpunct-bar-9 x0)) rest) = just (ParseTree (parsed-numpunct-bar-10 (string-append 0 x0)) ::' rest , 2)
len-dec-rewrite {- P79-} ((Id "P79") :: _::_(ParseTree (parsed-numpunct-bar-10 x0)) rest) = just (ParseTree (parsed-numpunct (string-append 0 x0)) ::' rest , 2)
len-dec-rewrite {- P8-} ((Id "P8") :: _::_(InputChar 'i') rest) = just (ParseTree (parsed-alpha-range-1 (string-append 0 (char-to-string 'i'))) ::' rest , 2)
len-dec-rewrite {- P80-} ((Id "P80") :: _::_(ParseTree (parsed-var x0)) rest) = just (ParseTree (parsed-qvar (string-append 0 x0)) ::' rest , 2)
len-dec-rewrite {- P81-} ((Id "P81") :: (ParseTree (parsed-var x0)) :: (InputChar '.') :: _::_(ParseTree (parsed-qvar x1)) rest) = just (ParseTree (parsed-qvar (string-append 2 x0 (char-to-string '.') x1)) ::' rest , 4)
len-dec-rewrite {- P82-} ((Id "P82") :: _::_(ParseTree (parsed-alpha x0)) rest) = just (ParseTree (parsed-var-bar-11 (string-append 0 x0)) ::' rest , 2)
len-dec-rewrite {- P83-} ((Id "P83") :: _::_(ParseTree (parsed-numpunct x0)) rest) = just (ParseTree (parsed-var-bar-11 (string-append 0 x0)) ::' rest , 2)
len-dec-rewrite {- P85-} ((Id "P85") :: (ParseTree (parsed-var-bar-11 x0)) :: _::_(ParseTree (parsed-var-star-12 x1)) rest) = just (ParseTree (parsed-var-star-12 (string-append 1 x0 x1)) ::' rest , 3)
len-dec-rewrite {- P86-} ((Id "P86") :: (ParseTree (parsed-alpha x0)) :: _::_(ParseTree (parsed-var-star-12 x1)) rest) = just (ParseTree (parsed-var (string-append 1 x0 x1)) ::' rest , 3)
len-dec-rewrite {- P87-} ((Id "P87") :: _::_(InputChar '_') rest) = just (ParseTree (parsed-bvar-bar-13 (string-append 0 (char-to-string '_'))) ::' rest , 2)
len-dec-rewrite {- P88-} ((Id "P88") :: _::_(ParseTree (parsed-var x0)) rest) = just (ParseTree (parsed-bvar-bar-13 (string-append 0 x0)) ::' rest , 2)
len-dec-rewrite {- P89-} ((Id "P89") :: _::_(ParseTree (parsed-bvar-bar-13 x0)) rest) = just (ParseTree (parsed-bvar (string-append 0 x0)) ::' rest , 2)
len-dec-rewrite {- P9-} ((Id "P9") :: _::_(InputChar 'j') rest) = just (ParseTree (parsed-alpha-range-1 (string-append 0 (char-to-string 'j'))) ::' rest , 2)
len-dec-rewrite {- P90-} ((Id "P90") :: (InputChar '.') :: (InputChar '.') :: _::_(InputChar '/') rest) = just (ParseTree (parsed-fpth-plus-14 (string-append 2 (char-to-string '.') (char-to-string '.') (char-to-string '/'))) ::' rest , 4)
len-dec-rewrite {- P91-} ((Id "P91") :: (InputChar '.') :: (InputChar '.') :: (InputChar '/') :: _::_(ParseTree (parsed-fpth-plus-14 x0)) rest) = just (ParseTree (parsed-fpth-plus-14 (string-append 3 (char-to-string '.') (char-to-string '.') (char-to-string '/') x0)) ::' rest , 5)
len-dec-rewrite {- P92-} ((Id "P92") :: _::_(ParseTree (parsed-alpha x0)) rest) = just (ParseTree (parsed-fpth-bar-15 (string-append 0 x0)) ::' rest , 2)
len-dec-rewrite {- P93-} ((Id "P93") :: _::_(ParseTree (parsed-fpth-plus-14 x0)) rest) = just (ParseTree (parsed-fpth-bar-15 (string-append 0 x0)) ::' rest , 2)
len-dec-rewrite {- P94-} ((Id "P94") :: _::_(ParseTree (parsed-numpunct x0)) rest) = just (ParseTree (parsed-fpth-bar-16 (string-append 0 x0)) ::' rest , 2)
len-dec-rewrite {- P95-} ((Id "P95") :: _::_(InputChar '/') rest) = just (ParseTree (parsed-fpth-bar-16 (string-append 0 (char-to-string '/'))) ::' rest , 2)
len-dec-rewrite {- P96-} ((Id "P96") :: _::_(ParseTree (parsed-alpha x0)) rest) = just (ParseTree (parsed-fpth-bar-17 (string-append 0 x0)) ::' rest , 2)
len-dec-rewrite {- P97-} ((Id "P97") :: _::_(ParseTree (parsed-fpth-bar-16 x0)) rest) = just (ParseTree (parsed-fpth-bar-17 (string-append 0 x0)) ::' rest , 2)
len-dec-rewrite {- P99-} ((Id "P99") :: (ParseTree (parsed-fpth-bar-17 x0)) :: _::_(ParseTree (parsed-fpth-star-18 x1)) rest) = just (ParseTree (parsed-fpth-star-18 (string-append 1 x0 x1)) ::' rest , 3)
len-dec-rewrite {- ParamsCons-} ((Id "ParamsCons") :: (ParseTree parsed-ows) :: (ParseTree (parsed-decl x0)) :: _::_(ParseTree (parsed-params x1)) rest) = just (ParseTree (parsed-params (norm-params (ParamsCons x0 x1))) ::' rest , 4)
len-dec-rewrite {- Parens-} ((Id "Parens") :: (ParseTree (parsed-posinfo x0)) :: (InputChar '(') :: (ParseTree parsed-ows) :: (ParseTree (parsed-term x1)) :: (ParseTree parsed-ows) :: (InputChar ')') :: _::_(ParseTree (parsed-posinfo x2)) rest) = just (ParseTree (parsed-pterm (norm-term (Parens x0 x1 x2))) ::' rest , 8)
len-dec-rewrite {- Pi-} ((Id "Pi") :: _::_(InputChar 'Π') rest) = just (ParseTree (parsed-binder (norm-binder Pi)) ::' rest , 2)
len-dec-rewrite {- Rho-} ((Id "Rho") :: (ParseTree (parsed-posinfo x0)) :: (ParseTree (parsed-rho x1)) :: (ParseTree parsed-ows) :: (ParseTree (parsed-lterm x2)) :: (ParseTree parsed-ows) :: (InputChar '-') :: (ParseTree parsed-ows) :: _::_(ParseTree (parsed-lterm x3)) rest) = just (ParseTree (parsed-lterm (norm-term (Rho x0 x1 x2 x3))) ::' rest , 9)
len-dec-rewrite {- RhoPlain-} ((Id "RhoPlain") :: _::_(InputChar 'ρ') rest) = just (ParseTree (parsed-rho (norm-rho RhoPlain)) ::' rest , 2)
len-dec-rewrite {- RhoPlus-} ((Id "RhoPlus") :: (InputChar 'ρ') :: _::_(InputChar '+') rest) = just (ParseTree (parsed-rho (norm-rho RhoPlus)) ::' rest , 3)
len-dec-rewrite {- Right-} ((Id "Right") :: _::_(InputChar 'r') rest) = just (ParseTree (parsed-leftRight (norm-leftRight Right)) ::' rest , 2)
len-dec-rewrite {- Sigma-} ((Id "Sigma") :: (ParseTree (parsed-posinfo x0)) :: (InputChar 'ς') :: (ParseTree parsed-ows) :: _::_(ParseTree (parsed-lterm x1)) rest) = just (ParseTree (parsed-lterm (norm-term (Sigma x0 x1))) ::' rest , 5)
len-dec-rewrite {- SomeClass-} ((Id "SomeClass") :: (ParseTree parsed-ows) :: (InputChar ':') :: (ParseTree parsed-ows) :: _::_(ParseTree (parsed-tk x0)) rest) = just (ParseTree (parsed-optClass (norm-optClass (SomeClass x0))) ::' rest , 5)
len-dec-rewrite {- SomeOptAs-} ((Id "SomeOptAs") :: (ParseTree parsed-ows) :: (InputChar 'a') :: (InputChar 's') :: (ParseTree parsed-ws) :: _::_(ParseTree (parsed-var x0)) rest) = just (ParseTree (parsed-optAs (norm-optAs (SomeOptAs x0))) ::' rest , 6)
len-dec-rewrite {- SomeTerm-} ((Id "SomeTerm") :: (ParseTree parsed-ows) :: (InputChar '{') :: (ParseTree parsed-ows) :: (ParseTree (parsed-term x0)) :: (ParseTree parsed-ows) :: (InputChar '}') :: _::_(ParseTree (parsed-posinfo x1)) rest) = just (ParseTree (parsed-optTerm (norm-optTerm (SomeTerm x0 x1))) ::' rest , 8)
len-dec-rewrite {- SomeType-} ((Id "SomeType") :: (ParseTree parsed-ows) :: (InputChar ':') :: (ParseTree parsed-ows) :: _::_(ParseTree (parsed-type x0)) rest) = just (ParseTree (parsed-optType (norm-optType (SomeType x0))) ::' rest , 5)
len-dec-rewrite {- Star-} ((Id "Star") :: (ParseTree (parsed-posinfo x0)) :: _::_(InputChar '★') rest) = just (ParseTree (parsed-kind (norm-kind (Star x0))) ::' rest , 3)
len-dec-rewrite {- TermArg-} ((Id "TermArg") :: (ParseTree parsed-ws) :: _::_(ParseTree (parsed-lterm x0)) rest) = just (ParseTree (parsed-arg (norm-arg (TermArg x0))) ::' rest , 3)
len-dec-rewrite {- Theta-} ((Id "Theta") :: (ParseTree (parsed-posinfo x0)) :: (ParseTree (parsed-theta x1)) :: (ParseTree parsed-ws) :: (ParseTree (parsed-lterm x2)) :: (ParseTree parsed-ows) :: _::_(ParseTree (parsed-lterms x3)) rest) = just (ParseTree (parsed-term (norm-term (Theta x0 x1 x2 x3))) ::' rest , 7)
len-dec-rewrite {- Tkk-} ((Id "Tkk") :: (ParseTree (parsed-kind x0)) :: _::_(Id "Tkk_end") rest) = just (ParseTree (parsed-tk (norm-tk (Tkk x0))) ::' rest , 3)
len-dec-rewrite {- Tkt-} ((Id "Tkt") :: _::_(ParseTree (parsed-type x0)) rest) = just (ParseTree (parsed-tk (norm-tk (Tkt x0))) ::' rest , 2)
len-dec-rewrite {- TpApp-} ((ParseTree (parsed-ltype x0)) :: (ParseTree parsed-ws) :: (InputChar '·') :: (ParseTree parsed-ws) :: _::_(ParseTree (parsed-atype x1)) rest) = just (ParseTree (parsed-ltype (norm-type (TpApp x0 x1))) ::' rest , 5)
len-dec-rewrite {- TpAppt-} ((ParseTree (parsed-ltype x0)) :: (ParseTree parsed-ws) :: _::_(ParseTree (parsed-lterm x1)) rest) = just (ParseTree (parsed-ltype (norm-type (TpAppt x0 x1))) ::' rest , 3)
len-dec-rewrite {- TpArrow-} ((Id "TpArrow") :: (ParseTree (parsed-ltype x0)) :: (ParseTree parsed-ows) :: (ParseTree (parsed-arrowtype x1)) :: (ParseTree parsed-ows) :: _::_(ParseTree (parsed-type x2)) rest) = just (ParseTree (parsed-type (norm-type (TpArrow x0 x1 x2))) ::' rest , 6)
len-dec-rewrite {- TpEq-} ((Id "TpEq") :: (ParseTree (parsed-term x0)) :: (ParseTree parsed-ows) :: (InputChar '≃') :: (ParseTree parsed-ows) :: _::_(ParseTree (parsed-term x1)) rest) = just (ParseTree (parsed-type (norm-type (TpEq x0 x1))) ::' rest , 6)
len-dec-rewrite {- TpHole-} ((Id "TpHole") :: (ParseTree (parsed-posinfo x0)) :: _::_(InputChar '●') rest) = just (ParseTree (parsed-atype (norm-type (TpHole x0))) ::' rest , 3)
len-dec-rewrite {- TpLambda-} ((Id "TpLambda") :: (ParseTree (parsed-posinfo x0)) :: (InputChar 'λ') :: (ParseTree parsed-ows) :: (ParseTree (parsed-posinfo x1)) :: (ParseTree (parsed-bvar x2)) :: (ParseTree parsed-ows) :: (InputChar ':') :: (ParseTree parsed-ows) :: (ParseTree (parsed-tk x3)) :: (ParseTree parsed-ows) :: (InputChar '.') :: (ParseTree parsed-ows) :: _::_(ParseTree (parsed-type x4)) rest) = just (ParseTree (parsed-type (norm-type (TpLambda x0 x1 x2 x3 x4))) ::' rest , 14)
len-dec-rewrite {- TpParens-} ((Id "TpParens") :: (ParseTree (parsed-posinfo x0)) :: (InputChar '(') :: (ParseTree parsed-ows) :: (ParseTree (parsed-type x1)) :: (ParseTree parsed-ows) :: (InputChar ')') :: _::_(ParseTree (parsed-posinfo x2)) rest) = just (ParseTree (parsed-atype (norm-type (TpParens x0 x1 x2))) ::' rest , 8)
len-dec-rewrite {- TpVar-} ((Id "TpVar") :: (ParseTree (parsed-posinfo x0)) :: _::_(ParseTree (parsed-qvar x1)) rest) = just (ParseTree (parsed-atype (norm-type (TpVar x0 x1))) ::' rest , 3)
len-dec-rewrite {- Type-} ((Id "Type") :: (ParseTree parsed-ows) :: (InputChar '◂') :: (ParseTree parsed-ows) :: _::_(ParseTree (parsed-type x0)) rest) = just (ParseTree (parsed-maybeCheckType (norm-maybeCheckType (Type x0))) ::' rest , 5)
len-dec-rewrite {- TypeArg-} ((Id "TypeArg") :: (ParseTree parsed-ows) :: (InputChar '·') :: (ParseTree parsed-ws) :: _::_(ParseTree (parsed-atype x0)) rest) = just (ParseTree (parsed-arg (norm-arg (TypeArg x0))) ::' rest , 5)
len-dec-rewrite {- UnerasedArrow-} ((Id "UnerasedArrow") :: _::_(InputChar '➔') rest) = just (ParseTree (parsed-arrowtype (norm-arrowtype UnerasedArrow)) ::' rest , 2)
len-dec-rewrite {- Var-} ((Id "Var") :: (ParseTree (parsed-posinfo x0)) :: _::_(ParseTree (parsed-qvar x1)) rest) = just (ParseTree (parsed-pterm (norm-term (Var x0 x1))) ::' rest , 3)
len-dec-rewrite {- VarsNext-} ((Id "VarsNext") :: (ParseTree (parsed-var x0)) :: (ParseTree parsed-ws) :: _::_(ParseTree (parsed-vars x1)) rest) = just (ParseTree (parsed-vars (norm-vars (VarsNext x0 x1))) ::' rest , 4)
len-dec-rewrite {- VarsStart-} ((Id "VarsStart") :: _::_(ParseTree (parsed-var x0)) rest) = just (ParseTree (parsed-vars (norm-vars (VarsStart x0))) ::' rest , 2)
len-dec-rewrite {- embed-} ((Id "embed") :: (ParseTree (parsed-aterm x0)) :: _::_(Id "embed_end") rest) = just (ParseTree (parsed-term x0) ::' rest , 3)
len-dec-rewrite {- embed-} ((Id "embed") :: _::_(ParseTree (parsed-lterm x0)) rest) = just (ParseTree (parsed-aterm x0) ::' rest , 2)
len-dec-rewrite {- embed-} ((Id "embed") :: (ParseTree (parsed-pterm x0)) :: _::_(Id "embed_end") rest) = just (ParseTree (parsed-lterm x0) ::' rest , 3)
len-dec-rewrite {- embed-} ((Id "embed") :: (ParseTree (parsed-ltype x0)) :: _::_(Id "embed_end") rest) = just (ParseTree (parsed-type x0) ::' rest , 3)
len-dec-rewrite {- embed-} ((Id "embed") :: _::_(ParseTree (parsed-atype x0)) rest) = just (ParseTree (parsed-ltype x0) ::' rest , 2)
len-dec-rewrite {- embed-} ((Id "embed") :: _::_(ParseTree (parsed-lliftingType x0)) rest) = just (ParseTree (parsed-liftingType x0) ::' rest , 2)
len-dec-rewrite {- Both-} (_::_(Id "Both") rest) = just (ParseTree (parsed-leftRight (norm-leftRight Both)) ::' rest , 1)
len-dec-rewrite {- CmdsStart-} (_::_(Id "CmdsStart") rest) = just (ParseTree (parsed-cmds (norm-cmds CmdsStart)) ::' rest , 1)
len-dec-rewrite {- EpsHnf-} (_::_(Id "EpsHnf") rest) = just (ParseTree (parsed-maybeMinus (norm-maybeMinus EpsHnf)) ::' rest , 1)
len-dec-rewrite {- ImportsStart-} (_::_(Id "ImportsStart") rest) = just (ParseTree (parsed-imports (norm-imports ImportsStart)) ::' rest , 1)
len-dec-rewrite {- NoAtype-} (_::_(Id "NoAtype") rest) = just (ParseTree (parsed-maybeAtype (norm-maybeAtype NoAtype)) ::' rest , 1)
len-dec-rewrite {- NoCheckType-} (_::_(Id "NoCheckType") rest) = just (ParseTree (parsed-maybeCheckType (norm-maybeCheckType NoCheckType)) ::' rest , 1)
len-dec-rewrite {- NoClass-} (_::_(Id "NoClass") rest) = just (ParseTree (parsed-optClass (norm-optClass NoClass)) ::' rest , 1)
len-dec-rewrite {- NoOptAs-} (_::_(Id "NoOptAs") rest) = just (ParseTree (parsed-optAs (norm-optAs NoOptAs)) ::' rest , 1)
len-dec-rewrite {- NoTerm-} (_::_(Id "NoTerm") rest) = just (ParseTree (parsed-optTerm (norm-optTerm NoTerm)) ::' rest , 1)
len-dec-rewrite {- NoType-} (_::_(Id "NoType") rest) = just (ParseTree (parsed-optType (norm-optType NoType)) ::' rest , 1)
len-dec-rewrite {- NotErased-} (_::_(Id "NotErased") rest) = just (ParseTree (parsed-maybeErased (norm-maybeErased NotErased)) ::' rest , 1)
len-dec-rewrite {- P105-} (_::_(Id "P105") rest) = just (ParseTree (parsed-kvar-star-20 empty-string) ::' rest , 1)
len-dec-rewrite {- P214-} (_::_(Id "P214") rest) = just (ParseTree parsed-comment-star-73 ::' rest , 1)
len-dec-rewrite {- P227-} (_::_(Id "P227") rest) = just (ParseTree parsed-ows-star-78 ::' rest , 1)
len-dec-rewrite {- P84-} (_::_(Id "P84") rest) = just (ParseTree (parsed-var-star-12 empty-string) ::' rest , 1)
len-dec-rewrite {- P98-} (_::_(Id "P98") rest) = just (ParseTree (parsed-fpth-star-18 empty-string) ::' rest , 1)
len-dec-rewrite {- ParamsNil-} (_::_(Id "ParamsNil") rest) = just (ParseTree (parsed-params (norm-params ParamsNil)) ::' rest , 1)
len-dec-rewrite {- Posinfo-} (_::_(Posinfo n) rest) = just (ParseTree (parsed-posinfo (ℕ-to-string n)) ::' rest , 1)
len-dec-rewrite x = nothing

rrs : rewriteRules
rrs = record { len-dec-rewrite = len-dec-rewrite }
