----------------------------------------------------------------------------------
-- Types for parse trees
----------------------------------------------------------------------------------

module huffman-types where

open import lib
open import parse-tree

posinfo = string
character = string
character-bar-3 = string
character-bar-4 = string
character-bar-5 = string
character-bar-6 = string
character-bar-7 = string
character-range-1 = string
character-range-2 = string
word = string

mutual

  data bvlit : Set where 
    BvlitCons : digit → bvlit → bvlit
    BvlitStart : digit → bvlit

  data cmd : Set where 
    Decode : codes → bvlit → cmd
    Encode : words → cmd

  data code : Set where 
    Code : word → bvlit → code

  data codes : Set where 
    CodesNext : code → codes → codes
    CodesStart : code → codes

  data digit : Set where 
    One : digit
    Zero : digit

  data start : Set where 
    File : cmd → start

  data words : Set where 
    WordsNext : word → words → words
    WordsStart : word → words

-- embedded types:

data ParseTreeT : Set where
  parsed-bvlit : bvlit → ParseTreeT
  parsed-cmd : cmd → ParseTreeT
  parsed-code : code → ParseTreeT
  parsed-codes : codes → ParseTreeT
  parsed-digit : digit → ParseTreeT
  parsed-start : start → ParseTreeT
  parsed-words : words → ParseTreeT
  parsed-posinfo : posinfo → ParseTreeT
  parsed-character : character → ParseTreeT
  parsed-character-bar-3 : character-bar-3 → ParseTreeT
  parsed-character-bar-4 : character-bar-4 → ParseTreeT
  parsed-character-bar-5 : character-bar-5 → ParseTreeT
  parsed-character-bar-6 : character-bar-6 → ParseTreeT
  parsed-character-bar-7 : character-bar-7 → ParseTreeT
  parsed-character-range-1 : character-range-1 → ParseTreeT
  parsed-character-range-2 : character-range-2 → ParseTreeT
  parsed-word : word → ParseTreeT
  parsed-aws : ParseTreeT
  parsed-aws-bar-8 : ParseTreeT
  parsed-aws-bar-9 : ParseTreeT
  parsed-ows : ParseTreeT
  parsed-ows-star-11 : ParseTreeT
  parsed-ws : ParseTreeT
  parsed-ws-plus-10 : ParseTreeT

------------------------------------------
-- Parse tree printing functions
------------------------------------------

posinfoToString : posinfo → string
posinfoToString x = "(posinfo " ^ x ^ ")"
characterToString : character → string
characterToString x = "(character " ^ x ^ ")"
character-bar-3ToString : character-bar-3 → string
character-bar-3ToString x = "(character-bar-3 " ^ x ^ ")"
character-bar-4ToString : character-bar-4 → string
character-bar-4ToString x = "(character-bar-4 " ^ x ^ ")"
character-bar-5ToString : character-bar-5 → string
character-bar-5ToString x = "(character-bar-5 " ^ x ^ ")"
character-bar-6ToString : character-bar-6 → string
character-bar-6ToString x = "(character-bar-6 " ^ x ^ ")"
character-bar-7ToString : character-bar-7 → string
character-bar-7ToString x = "(character-bar-7 " ^ x ^ ")"
character-range-1ToString : character-range-1 → string
character-range-1ToString x = "(character-range-1 " ^ x ^ ")"
character-range-2ToString : character-range-2 → string
character-range-2ToString x = "(character-range-2 " ^ x ^ ")"
wordToString : word → string
wordToString x = "(word " ^ x ^ ")"

mutual
  bvlitToString : bvlit → string
  bvlitToString (BvlitCons x0 x1) = "(BvlitCons" ^ " " ^ (digitToString x0) ^ " " ^ (bvlitToString x1) ^ ")"
  bvlitToString (BvlitStart x0) = "(BvlitStart" ^ " " ^ (digitToString x0) ^ ")"

  cmdToString : cmd → string
  cmdToString (Decode x0 x1) = "(Decode" ^ " " ^ (codesToString x0) ^ " " ^ (bvlitToString x1) ^ ")"
  cmdToString (Encode x0) = "(Encode" ^ " " ^ (wordsToString x0) ^ ")"

  codeToString : code → string
  codeToString (Code x0 x1) = "(Code" ^ " " ^ (wordToString x0) ^ " " ^ (bvlitToString x1) ^ ")"

  codesToString : codes → string
  codesToString (CodesNext x0 x1) = "(CodesNext" ^ " " ^ (codeToString x0) ^ " " ^ (codesToString x1) ^ ")"
  codesToString (CodesStart x0) = "(CodesStart" ^ " " ^ (codeToString x0) ^ ")"

  digitToString : digit → string
  digitToString (One) = "One" ^ ""
  digitToString (Zero) = "Zero" ^ ""

  startToString : start → string
  startToString (File x0) = "(File" ^ " " ^ (cmdToString x0) ^ ")"

  wordsToString : words → string
  wordsToString (WordsNext x0 x1) = "(WordsNext" ^ " " ^ (wordToString x0) ^ " " ^ (wordsToString x1) ^ ")"
  wordsToString (WordsStart x0) = "(WordsStart" ^ " " ^ (wordToString x0) ^ ")"

ParseTreeToString : ParseTreeT → string
ParseTreeToString (parsed-bvlit t) = bvlitToString t
ParseTreeToString (parsed-cmd t) = cmdToString t
ParseTreeToString (parsed-code t) = codeToString t
ParseTreeToString (parsed-codes t) = codesToString t
ParseTreeToString (parsed-digit t) = digitToString t
ParseTreeToString (parsed-start t) = startToString t
ParseTreeToString (parsed-words t) = wordsToString t
ParseTreeToString (parsed-posinfo t) = posinfoToString t
ParseTreeToString (parsed-character t) = characterToString t
ParseTreeToString (parsed-character-bar-3 t) = character-bar-3ToString t
ParseTreeToString (parsed-character-bar-4 t) = character-bar-4ToString t
ParseTreeToString (parsed-character-bar-5 t) = character-bar-5ToString t
ParseTreeToString (parsed-character-bar-6 t) = character-bar-6ToString t
ParseTreeToString (parsed-character-bar-7 t) = character-bar-7ToString t
ParseTreeToString (parsed-character-range-1 t) = character-range-1ToString t
ParseTreeToString (parsed-character-range-2 t) = character-range-2ToString t
ParseTreeToString (parsed-word t) = wordToString t
ParseTreeToString parsed-aws = "[aws]"
ParseTreeToString parsed-aws-bar-8 = "[aws-bar-8]"
ParseTreeToString parsed-aws-bar-9 = "[aws-bar-9]"
ParseTreeToString parsed-ows = "[ows]"
ParseTreeToString parsed-ows-star-11 = "[ows-star-11]"
ParseTreeToString parsed-ws = "[ws]"
ParseTreeToString parsed-ws-plus-10 = "[ws-plus-10]"

------------------------------------------
-- Reorganizing rules
------------------------------------------

mutual

  {-# NO_TERMINATION_CHECK #-}
  norm-words : (x : words) → words
  norm-words x = x

  {-# NO_TERMINATION_CHECK #-}
  norm-start : (x : start) → start
  norm-start x = x

  {-# NO_TERMINATION_CHECK #-}
  norm-posinfo : (x : posinfo) → posinfo
  norm-posinfo x = x

  {-# NO_TERMINATION_CHECK #-}
  norm-digit : (x : digit) → digit
  norm-digit x = x

  {-# NO_TERMINATION_CHECK #-}
  norm-codes : (x : codes) → codes
  norm-codes x = x

  {-# NO_TERMINATION_CHECK #-}
  norm-code : (x : code) → code
  norm-code x = x

  {-# NO_TERMINATION_CHECK #-}
  norm-cmd : (x : cmd) → cmd
  norm-cmd x = x

  {-# NO_TERMINATION_CHECK #-}
  norm-bvlit : (x : bvlit) → bvlit
  norm-bvlit x = x

isParseTree : ParseTreeT → 𝕃 char → string → Set
isParseTree p l s = ⊤ {- this will be ignored since we are using simply typed runs -}

ptr : ParseTreeRec
ptr = record { ParseTreeT = ParseTreeT ; isParseTree = isParseTree ; ParseTreeToString = ParseTreeToString }

