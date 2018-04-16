----------------------------------------------------------------------------------
-- Types for parse trees
----------------------------------------------------------------------------------

module cws-types where

open import lib
open import parse-tree

posinfo = string

{-# IMPORT CedilleCommentsLexer #-}

data entity : Set where 
    EntityComment : posinfo → posinfo → entity
    EntityNonws : entity
    EntityWs : posinfo → posinfo → entity
{-# COMPILED_DATA entity CedilleCommentsLexer.Entity CedilleCommentsLexer.EntityComment  CedilleCommentsLexer.EntityNonws CedilleCommentsLexer.EntityWs #-}

data entities : Set where 
    EndEntity : entities
    Entity : entity → entities → entities
{-# COMPILED_DATA entities CedilleCommentsLexer.Entities CedilleCommentsLexer.EndEntity  CedilleCommentsLexer.Entity #-}

data start : Set where 
    File : entities → start
{-# COMPILED_DATA start CedilleCommentsLexer.Start CedilleCommentsLexer.File #-}

postulate
  scanComments  : string → start

{-# COMPILED scanComments CedilleCommentsLexer.scanComments #-}

-- embedded types:

data ParseTreeT : Set where
  parsed-entities : entities → ParseTreeT
  parsed-entity : entity → ParseTreeT
  parsed-start : start → ParseTreeT
  parsed-posinfo : posinfo → ParseTreeT
  parsed-alpha : ParseTreeT
  parsed-alpha-bar-3 : ParseTreeT
  parsed-alpha-range-1 : ParseTreeT
  parsed-alpha-range-2 : ParseTreeT
  parsed-anychar : ParseTreeT
  parsed-anychar-bar-59 : ParseTreeT
  parsed-anychar-bar-60 : ParseTreeT
  parsed-anychar-bar-61 : ParseTreeT
  parsed-anychar-bar-62 : ParseTreeT
  parsed-anychar-bar-63 : ParseTreeT
  parsed-anynonwschar : ParseTreeT
  parsed-anynonwschar-bar-68 : ParseTreeT
  parsed-anynonwschar-bar-69 : ParseTreeT
  parsed-aws : ParseTreeT
  parsed-aws-bar-65 : ParseTreeT
  parsed-aws-bar-66 : ParseTreeT
  parsed-comment : ParseTreeT
  parsed-comment-star-64 : ParseTreeT
  parsed-nonws : ParseTreeT
  parsed-nonws-plus-70 : ParseTreeT
  parsed-num : ParseTreeT
  parsed-num-plus-5 : ParseTreeT
  parsed-numone : ParseTreeT
  parsed-numone-range-4 : ParseTreeT
  parsed-numpunct : ParseTreeT
  parsed-numpunct-bar-10 : ParseTreeT
  parsed-numpunct-bar-11 : ParseTreeT
  parsed-numpunct-bar-6 : ParseTreeT
  parsed-numpunct-bar-7 : ParseTreeT
  parsed-numpunct-bar-8 : ParseTreeT
  parsed-numpunct-bar-9 : ParseTreeT
  parsed-otherpunct : ParseTreeT
  parsed-otherpunct-bar-12 : ParseTreeT
  parsed-otherpunct-bar-13 : ParseTreeT
  parsed-otherpunct-bar-14 : ParseTreeT
  parsed-otherpunct-bar-15 : ParseTreeT
  parsed-otherpunct-bar-16 : ParseTreeT
  parsed-otherpunct-bar-17 : ParseTreeT
  parsed-otherpunct-bar-18 : ParseTreeT
  parsed-otherpunct-bar-19 : ParseTreeT
  parsed-otherpunct-bar-20 : ParseTreeT
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
  parsed-ws : ParseTreeT
  parsed-ws-plus-67 : ParseTreeT

------------------------------------------
-- Parse tree printing functions
------------------------------------------

posinfoToString : posinfo → string
posinfoToString x = "(posinfo " ^ x ^ ")"

mutual
  entitiesToString : entities → string
  entitiesToString (EndEntity) = "EndEntity" ^ ""
  entitiesToString (Entity x0 x1) = "(Entity" ^ " " ^ (entityToString x0) ^ " " ^ (entitiesToString x1) ^ ")"

  entityToString : entity → string
  entityToString (EntityComment x0 x1) = "(EntityComment" ^ " " ^ (posinfoToString x0) ^ " " ^ (posinfoToString x1) ^ ")"
  entityToString (EntityNonws) = "EntityNonws" ^ ""
  entityToString (EntityWs x0 x1) = "(EntityWs" ^ " " ^ (posinfoToString x0) ^ " " ^ (posinfoToString x1) ^ ")"

  startToString : start → string
  startToString (File x0) = "(File" ^ " " ^ (entitiesToString x0) ^ ")"

ParseTreeToString : ParseTreeT → string
ParseTreeToString (parsed-entities t) = entitiesToString t
ParseTreeToString (parsed-entity t) = entityToString t
ParseTreeToString (parsed-start t) = startToString t
ParseTreeToString (parsed-posinfo t) = posinfoToString t
ParseTreeToString parsed-alpha = "[alpha]"
ParseTreeToString parsed-alpha-bar-3 = "[alpha-bar-3]"
ParseTreeToString parsed-alpha-range-1 = "[alpha-range-1]"
ParseTreeToString parsed-alpha-range-2 = "[alpha-range-2]"
ParseTreeToString parsed-anychar = "[anychar]"
ParseTreeToString parsed-anychar-bar-59 = "[anychar-bar-59]"
ParseTreeToString parsed-anychar-bar-60 = "[anychar-bar-60]"
ParseTreeToString parsed-anychar-bar-61 = "[anychar-bar-61]"
ParseTreeToString parsed-anychar-bar-62 = "[anychar-bar-62]"
ParseTreeToString parsed-anychar-bar-63 = "[anychar-bar-63]"
ParseTreeToString parsed-anynonwschar = "[anynonwschar]"
ParseTreeToString parsed-anynonwschar-bar-68 = "[anynonwschar-bar-68]"
ParseTreeToString parsed-anynonwschar-bar-69 = "[anynonwschar-bar-69]"
ParseTreeToString parsed-aws = "[aws]"
ParseTreeToString parsed-aws-bar-65 = "[aws-bar-65]"
ParseTreeToString parsed-aws-bar-66 = "[aws-bar-66]"
ParseTreeToString parsed-comment = "[comment]"
ParseTreeToString parsed-comment-star-64 = "[comment-star-64]"
ParseTreeToString parsed-nonws = "[nonws]"
ParseTreeToString parsed-nonws-plus-70 = "[nonws-plus-70]"
ParseTreeToString parsed-num = "[num]"
ParseTreeToString parsed-num-plus-5 = "[num-plus-5]"
ParseTreeToString parsed-numone = "[numone]"
ParseTreeToString parsed-numone-range-4 = "[numone-range-4]"
ParseTreeToString parsed-numpunct = "[numpunct]"
ParseTreeToString parsed-numpunct-bar-10 = "[numpunct-bar-10]"
ParseTreeToString parsed-numpunct-bar-11 = "[numpunct-bar-11]"
ParseTreeToString parsed-numpunct-bar-6 = "[numpunct-bar-6]"
ParseTreeToString parsed-numpunct-bar-7 = "[numpunct-bar-7]"
ParseTreeToString parsed-numpunct-bar-8 = "[numpunct-bar-8]"
ParseTreeToString parsed-numpunct-bar-9 = "[numpunct-bar-9]"
ParseTreeToString parsed-otherpunct = "[otherpunct]"
ParseTreeToString parsed-otherpunct-bar-12 = "[otherpunct-bar-12]"
ParseTreeToString parsed-otherpunct-bar-13 = "[otherpunct-bar-13]"
ParseTreeToString parsed-otherpunct-bar-14 = "[otherpunct-bar-14]"
ParseTreeToString parsed-otherpunct-bar-15 = "[otherpunct-bar-15]"
ParseTreeToString parsed-otherpunct-bar-16 = "[otherpunct-bar-16]"
ParseTreeToString parsed-otherpunct-bar-17 = "[otherpunct-bar-17]"
ParseTreeToString parsed-otherpunct-bar-18 = "[otherpunct-bar-18]"
ParseTreeToString parsed-otherpunct-bar-19 = "[otherpunct-bar-19]"
ParseTreeToString parsed-otherpunct-bar-20 = "[otherpunct-bar-20]"
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
ParseTreeToString parsed-ws = "[ws]"
ParseTreeToString parsed-ws-plus-67 = "[ws-plus-67]"

------------------------------------------
-- Reorganizing rules
------------------------------------------

mutual

  {-# TERMINATING #-}
  norm-start : (x : start) → start
  norm-start x = x

  {-# TERMINATING #-}
  norm-posinfo : (x : posinfo) → posinfo
  norm-posinfo x = x

  {-# TERMINATING #-}
  norm-entity : (x : entity) → entity
  norm-entity x = x

  {-# TERMINATING #-}
  norm-entities : (x : entities) → entities
  norm-entities x = x

isParseTree : ParseTreeT → 𝕃 char → string → Set
isParseTree p l s = ⊤ {- this will be ignored since we are using simply typed runs -}

ptr : ParseTreeRec
ptr = record { ParseTreeT = ParseTreeT ; isParseTree = isParseTree ; ParseTreeToString = ParseTreeToString }

