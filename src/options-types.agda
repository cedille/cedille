----------------------------------------------------------------------------------
-- Types for parse trees
----------------------------------------------------------------------------------

module options-types where

open import lib
open import parse-tree

posinfo = string
alpha = string
alpha-bar-4 = string
alpha-range-2 = string
alpha-range-3 = string
anychar = string
anychar-bar-10 = string
anychar-bar-11 = string
anychar-bar-12 = string
anychar-bar-13 = string
anychar-bar-14 = string
anychar-bar-15 = string
anychar-bar-16 = string
anychar-bar-17 = string
anychar-bar-18 = string
anychar-bar-19 = string
anychar-bar-20 = string
anychar-bar-21 = string
anychar-bar-22 = string
anychar-bar-23 = string
anychar-bar-24 = string
anychar-bar-25 = string
anychar-bar-26 = string
anychar-bar-27 = string
anychar-bar-28 = string
anychar-bar-29 = string
anychar-bar-9 = string
num = string
num-plus-6 = string
numone = string
numone-range-5 = string
numpunct = string
numpunct-bar-7 = string
numpunct-bar-8 = string
path = string
path-star-1 = string

{-# IMPORT CedilleOptionsParser #-}
{-# IMPORT CedilleOptionsLexer #-}

data str-bool : Set where 
    StrBoolFalse : str-bool
    StrBoolTrue : str-bool
{-# COMPILED_DATA str-bool CedilleOptionsLexer.StrBool CedilleOptionsLexer.StrBoolFalse CedilleOptionsLexer.StrBoolTrue #-}

data paths : Set where 
    PathsCons : path → paths → paths
    PathsNil : paths
{-# COMPILED_DATA paths CedilleOptionsLexer.Paths CedilleOptionsLexer.PathsCons CedilleOptionsLexer.PathsNil #-}

data opt : Set where 
    GenerateLogs : str-bool → opt
    Lib : paths → opt
    MakeCoreFiles : str-bool → opt
    MakeRktFiles : str-bool → opt
    ShowQualifiedVars : str-bool → opt
    UseCedeFiles : str-bool → opt
{-# COMPILED_DATA opt CedilleOptionsLexer.Opt CedilleOptionsLexer.GenerateLogs CedilleOptionsLexer.Lib CedilleOptionsLexer.MakeCoreFiles CedilleOptionsLexer.MakeRktFiles CedilleOptionsLexer.ShowQualifiedVars CedilleOptionsLexer.UseCedeFiles #-}

data opts : Set where 
    OptsCons : opt → opts → opts
    OptsNil : opts
{-# COMPILED_DATA opts CedilleOptionsLexer.Opts CedilleOptionsLexer.OptsCons CedilleOptionsLexer.OptsNil #-}    

data start : Set where 
    File : opts → start
{-# COMPILED_DATA start CedilleOptionsLexer.Start CedilleOptionsLexer.File #-}

data Either (A : Set)(B : Set) : Set where
  Left : A → Either A B
  Right : B → Either A B
{-# COMPILED_DATA Either Either Left Right #-}

postulate
  scanOptions  : string → Either string start

{-# COMPILED scanOptions CedilleOptionsParser.parseOptions #-}

-- embedded types:

data ParseTreeT : Set where
  parsed-opt : opt → ParseTreeT
  parsed-opts : opts → ParseTreeT
  parsed-paths : paths → ParseTreeT
  parsed-start : start → ParseTreeT
  parsed-str-bool : str-bool → ParseTreeT
  parsed-posinfo : posinfo → ParseTreeT
  parsed-alpha : alpha → ParseTreeT
  parsed-alpha-bar-4 : alpha-bar-4 → ParseTreeT
  parsed-alpha-range-2 : alpha-range-2 → ParseTreeT
  parsed-alpha-range-3 : alpha-range-3 → ParseTreeT
  parsed-anychar : anychar → ParseTreeT
  parsed-anychar-bar-10 : anychar-bar-10 → ParseTreeT
  parsed-anychar-bar-11 : anychar-bar-11 → ParseTreeT
  parsed-anychar-bar-12 : anychar-bar-12 → ParseTreeT
  parsed-anychar-bar-13 : anychar-bar-13 → ParseTreeT
  parsed-anychar-bar-14 : anychar-bar-14 → ParseTreeT
  parsed-anychar-bar-15 : anychar-bar-15 → ParseTreeT
  parsed-anychar-bar-16 : anychar-bar-16 → ParseTreeT
  parsed-anychar-bar-17 : anychar-bar-17 → ParseTreeT
  parsed-anychar-bar-18 : anychar-bar-18 → ParseTreeT
  parsed-anychar-bar-19 : anychar-bar-19 → ParseTreeT
  parsed-anychar-bar-20 : anychar-bar-20 → ParseTreeT
  parsed-anychar-bar-21 : anychar-bar-21 → ParseTreeT
  parsed-anychar-bar-22 : anychar-bar-22 → ParseTreeT
  parsed-anychar-bar-23 : anychar-bar-23 → ParseTreeT
  parsed-anychar-bar-24 : anychar-bar-24 → ParseTreeT
  parsed-anychar-bar-25 : anychar-bar-25 → ParseTreeT
  parsed-anychar-bar-26 : anychar-bar-26 → ParseTreeT
  parsed-anychar-bar-27 : anychar-bar-27 → ParseTreeT
  parsed-anychar-bar-28 : anychar-bar-28 → ParseTreeT
  parsed-anychar-bar-29 : anychar-bar-29 → ParseTreeT
  parsed-anychar-bar-9 : anychar-bar-9 → ParseTreeT
  parsed-num : num → ParseTreeT
  parsed-num-plus-6 : num-plus-6 → ParseTreeT
  parsed-numone : numone → ParseTreeT
  parsed-numone-range-5 : numone-range-5 → ParseTreeT
  parsed-numpunct : numpunct → ParseTreeT
  parsed-numpunct-bar-7 : numpunct-bar-7 → ParseTreeT
  parsed-numpunct-bar-8 : numpunct-bar-8 → ParseTreeT
  parsed-path : path → ParseTreeT
  parsed-path-star-1 : path-star-1 → ParseTreeT
  parsed-aws : ParseTreeT
  parsed-aws-bar-31 : ParseTreeT
  parsed-aws-bar-32 : ParseTreeT
  parsed-aws-bar-33 : ParseTreeT
  parsed-comment : ParseTreeT
  parsed-comment-star-30 : ParseTreeT
  parsed-ows : ParseTreeT
  parsed-ows-star-35 : ParseTreeT
  parsed-squote : ParseTreeT
  parsed-ws : ParseTreeT
  parsed-ws-plus-34 : ParseTreeT

------------------------------------------
-- Parse tree printing functions
------------------------------------------

posinfoToString : posinfo → string
posinfoToString x = "(posinfo " ^ x ^ ")"
alphaToString : alpha → string
alphaToString x = "(alpha " ^ x ^ ")"
alpha-bar-4ToString : alpha-bar-4 → string
alpha-bar-4ToString x = "(alpha-bar-4 " ^ x ^ ")"
alpha-range-2ToString : alpha-range-2 → string
alpha-range-2ToString x = "(alpha-range-2 " ^ x ^ ")"
alpha-range-3ToString : alpha-range-3 → string
alpha-range-3ToString x = "(alpha-range-3 " ^ x ^ ")"
anycharToString : anychar → string
anycharToString x = "(anychar " ^ x ^ ")"
anychar-bar-10ToString : anychar-bar-10 → string
anychar-bar-10ToString x = "(anychar-bar-10 " ^ x ^ ")"
anychar-bar-11ToString : anychar-bar-11 → string
anychar-bar-11ToString x = "(anychar-bar-11 " ^ x ^ ")"
anychar-bar-12ToString : anychar-bar-12 → string
anychar-bar-12ToString x = "(anychar-bar-12 " ^ x ^ ")"
anychar-bar-13ToString : anychar-bar-13 → string
anychar-bar-13ToString x = "(anychar-bar-13 " ^ x ^ ")"
anychar-bar-14ToString : anychar-bar-14 → string
anychar-bar-14ToString x = "(anychar-bar-14 " ^ x ^ ")"
anychar-bar-15ToString : anychar-bar-15 → string
anychar-bar-15ToString x = "(anychar-bar-15 " ^ x ^ ")"
anychar-bar-16ToString : anychar-bar-16 → string
anychar-bar-16ToString x = "(anychar-bar-16 " ^ x ^ ")"
anychar-bar-17ToString : anychar-bar-17 → string
anychar-bar-17ToString x = "(anychar-bar-17 " ^ x ^ ")"
anychar-bar-18ToString : anychar-bar-18 → string
anychar-bar-18ToString x = "(anychar-bar-18 " ^ x ^ ")"
anychar-bar-19ToString : anychar-bar-19 → string
anychar-bar-19ToString x = "(anychar-bar-19 " ^ x ^ ")"
anychar-bar-20ToString : anychar-bar-20 → string
anychar-bar-20ToString x = "(anychar-bar-20 " ^ x ^ ")"
anychar-bar-21ToString : anychar-bar-21 → string
anychar-bar-21ToString x = "(anychar-bar-21 " ^ x ^ ")"
anychar-bar-22ToString : anychar-bar-22 → string
anychar-bar-22ToString x = "(anychar-bar-22 " ^ x ^ ")"
anychar-bar-23ToString : anychar-bar-23 → string
anychar-bar-23ToString x = "(anychar-bar-23 " ^ x ^ ")"
anychar-bar-24ToString : anychar-bar-24 → string
anychar-bar-24ToString x = "(anychar-bar-24 " ^ x ^ ")"
anychar-bar-25ToString : anychar-bar-25 → string
anychar-bar-25ToString x = "(anychar-bar-25 " ^ x ^ ")"
anychar-bar-26ToString : anychar-bar-26 → string
anychar-bar-26ToString x = "(anychar-bar-26 " ^ x ^ ")"
anychar-bar-27ToString : anychar-bar-27 → string
anychar-bar-27ToString x = "(anychar-bar-27 " ^ x ^ ")"
anychar-bar-28ToString : anychar-bar-28 → string
anychar-bar-28ToString x = "(anychar-bar-28 " ^ x ^ ")"
anychar-bar-29ToString : anychar-bar-29 → string
anychar-bar-29ToString x = "(anychar-bar-29 " ^ x ^ ")"
anychar-bar-9ToString : anychar-bar-9 → string
anychar-bar-9ToString x = "(anychar-bar-9 " ^ x ^ ")"
numToString : num → string
numToString x = "(num " ^ x ^ ")"
num-plus-6ToString : num-plus-6 → string
num-plus-6ToString x = "(num-plus-6 " ^ x ^ ")"
numoneToString : numone → string
numoneToString x = "(numone " ^ x ^ ")"
numone-range-5ToString : numone-range-5 → string
numone-range-5ToString x = "(numone-range-5 " ^ x ^ ")"
numpunctToString : numpunct → string
numpunctToString x = "(numpunct " ^ x ^ ")"
numpunct-bar-7ToString : numpunct-bar-7 → string
numpunct-bar-7ToString x = "(numpunct-bar-7 " ^ x ^ ")"
numpunct-bar-8ToString : numpunct-bar-8 → string
numpunct-bar-8ToString x = "(numpunct-bar-8 " ^ x ^ ")"
pathToString : path → string
pathToString x = "(path " ^ x ^ ")"
path-star-1ToString : path-star-1 → string
path-star-1ToString x = "(path-star-1 " ^ x ^ ")"

mutual
  optToString : opt → string
  optToString (GenerateLogs x0) = "(GenerateLogs" ^ " " ^ (str-boolToString x0) ^ ")"
  optToString (Lib x0) = "(Lib" ^ " " ^ (pathsToString x0) ^ ")"
  optToString (MakeCoreFiles x0) = "(MakeRktFiles" ^ " " ^ (str-boolToString x0) ^ ")"
  optToString (MakeRktFiles x0) = "(MakeRktFiles" ^ " " ^ (str-boolToString x0) ^ ")"
  optToString (ShowQualifiedVars x0) = "(ShowQualifiedVars" ^ " " ^ (str-boolToString x0) ^ ")"
  optToString (UseCedeFiles x0) = "(UseCedeFiles" ^ " " ^ (str-boolToString x0) ^ ")"

  optsToString : opts → string
  optsToString (OptsCons x0 x1) = "(OptsCons" ^ " " ^ (optToString x0) ^ " " ^ (optsToString x1) ^ ")"
  optsToString (OptsNil) = "OptsNil" ^ ""

  pathsToString : paths → string
  pathsToString (PathsCons x0 x1) = "(PathsCons" ^ " " ^ (pathToString x0) ^ " " ^ (pathsToString x1) ^ ")"
  pathsToString (PathsNil) = "PathsNil" ^ ""

  startToString : start → string
  startToString (File x0) = "(File" ^ " " ^ (optsToString x0) ^ ")"

  str-boolToString : str-bool → string
  str-boolToString (StrBoolFalse) = "StrBoolFalse" ^ ""
  str-boolToString (StrBoolTrue) = "StrBoolTrue" ^ ""

ParseTreeToString : ParseTreeT → string
ParseTreeToString (parsed-opt t) = optToString t
ParseTreeToString (parsed-opts t) = optsToString t
ParseTreeToString (parsed-paths t) = pathsToString t
ParseTreeToString (parsed-start t) = startToString t
ParseTreeToString (parsed-str-bool t) = str-boolToString t
ParseTreeToString (parsed-posinfo t) = posinfoToString t
ParseTreeToString (parsed-alpha t) = alphaToString t
ParseTreeToString (parsed-alpha-bar-4 t) = alpha-bar-4ToString t
ParseTreeToString (parsed-alpha-range-2 t) = alpha-range-2ToString t
ParseTreeToString (parsed-alpha-range-3 t) = alpha-range-3ToString t
ParseTreeToString (parsed-anychar t) = anycharToString t
ParseTreeToString (parsed-anychar-bar-10 t) = anychar-bar-10ToString t
ParseTreeToString (parsed-anychar-bar-11 t) = anychar-bar-11ToString t
ParseTreeToString (parsed-anychar-bar-12 t) = anychar-bar-12ToString t
ParseTreeToString (parsed-anychar-bar-13 t) = anychar-bar-13ToString t
ParseTreeToString (parsed-anychar-bar-14 t) = anychar-bar-14ToString t
ParseTreeToString (parsed-anychar-bar-15 t) = anychar-bar-15ToString t
ParseTreeToString (parsed-anychar-bar-16 t) = anychar-bar-16ToString t
ParseTreeToString (parsed-anychar-bar-17 t) = anychar-bar-17ToString t
ParseTreeToString (parsed-anychar-bar-18 t) = anychar-bar-18ToString t
ParseTreeToString (parsed-anychar-bar-19 t) = anychar-bar-19ToString t
ParseTreeToString (parsed-anychar-bar-20 t) = anychar-bar-20ToString t
ParseTreeToString (parsed-anychar-bar-21 t) = anychar-bar-21ToString t
ParseTreeToString (parsed-anychar-bar-22 t) = anychar-bar-22ToString t
ParseTreeToString (parsed-anychar-bar-23 t) = anychar-bar-23ToString t
ParseTreeToString (parsed-anychar-bar-24 t) = anychar-bar-24ToString t
ParseTreeToString (parsed-anychar-bar-25 t) = anychar-bar-25ToString t
ParseTreeToString (parsed-anychar-bar-26 t) = anychar-bar-26ToString t
ParseTreeToString (parsed-anychar-bar-27 t) = anychar-bar-27ToString t
ParseTreeToString (parsed-anychar-bar-28 t) = anychar-bar-28ToString t
ParseTreeToString (parsed-anychar-bar-29 t) = anychar-bar-29ToString t
ParseTreeToString (parsed-anychar-bar-9 t) = anychar-bar-9ToString t
ParseTreeToString (parsed-num t) = numToString t
ParseTreeToString (parsed-num-plus-6 t) = num-plus-6ToString t
ParseTreeToString (parsed-numone t) = numoneToString t
ParseTreeToString (parsed-numone-range-5 t) = numone-range-5ToString t
ParseTreeToString (parsed-numpunct t) = numpunctToString t
ParseTreeToString (parsed-numpunct-bar-7 t) = numpunct-bar-7ToString t
ParseTreeToString (parsed-numpunct-bar-8 t) = numpunct-bar-8ToString t
ParseTreeToString (parsed-path t) = pathToString t
ParseTreeToString (parsed-path-star-1 t) = path-star-1ToString t
ParseTreeToString parsed-aws = "[aws]"
ParseTreeToString parsed-aws-bar-31 = "[aws-bar-31]"
ParseTreeToString parsed-aws-bar-32 = "[aws-bar-32]"
ParseTreeToString parsed-aws-bar-33 = "[aws-bar-33]"
ParseTreeToString parsed-comment = "[comment]"
ParseTreeToString parsed-comment-star-30 = "[comment-star-30]"
ParseTreeToString parsed-ows = "[ows]"
ParseTreeToString parsed-ows-star-35 = "[ows-star-35]"
ParseTreeToString parsed-squote = "[squote]"
ParseTreeToString parsed-ws = "[ws]"
ParseTreeToString parsed-ws-plus-34 = "[ws-plus-34]"

------------------------------------------
-- Reorganizing rules
------------------------------------------

mutual

  {-# TERMINATING #-}
  norm-str-bool : (x : str-bool) → str-bool
  norm-str-bool x = x

  {-# TERMINATING #-}
  norm-start : (x : start) → start
  norm-start x = x

  {-# TERMINATING #-}
  norm-posinfo : (x : posinfo) → posinfo
  norm-posinfo x = x

  {-# TERMINATING #-}
  norm-paths : (x : paths) → paths
  norm-paths x = x

  {-# TERMINATING #-}
  norm-opts : (x : opts) → opts
  norm-opts x = x

  {-# TERMINATING #-}
  norm-opt : (x : opt) → opt
  norm-opt x = x

isParseTree : ParseTreeT → 𝕃 char → string → Set
isParseTree p l s = ⊤ {- this will be ignored since we are using simply typed runs -}

ptr : ParseTreeRec
ptr = record { ParseTreeT = ParseTreeT ; isParseTree = isParseTree ; ParseTreeToString = ParseTreeToString }

