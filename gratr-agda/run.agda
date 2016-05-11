open import parse-tree
open import string

module run (ptr : ParseTreeRec)  where

open import lib
open import datatypes

open ParseTreeRec ptr

module deriv where
  data RunElement : 𝕃 char → Set where
    Id : string → RunElement []
    InputChar : (c : char) → RunElement (c :: [])
    ParseTree : {l : 𝕃 char}{s : string}{pt : ParseTreeT} → isParseTree pt l s → RunElement l

  infixr 6 _::'_

  data Run : (ls : 𝕃 char) → Set where
    []' : Run []
    _::'_ : {lc elc : 𝕃 char} → RunElement elc → Run lc → Run (elc ++ lc)

  length-run : {lc : 𝕃 char} → Run lc → ℕ
  length-run []' = 0
  length-run (x ::' xs) = suc (length-run xs)

  RunElement-to-string : {lc : 𝕃 char} → RunElement lc → string
  RunElement-to-string (Id s) = ("id:" ^ s)
  RunElement-to-string (InputChar c) = "#" ^ (char-to-string c)
  RunElement-to-string (ParseTree{pt = pt} ipt) = (ParseTreeToString pt)

  Run-to-string : {lc : 𝕃 char} → Run lc → string
  Run-to-string []' = "\n"
  Run-to-string (e ::' r) =  (RunElement-to-string e) ^ " " ^ (Run-to-string r) 

  assocRun : (ls : 𝕃 (𝕃 char))(lc : 𝕃 char) → Run ((concat ls) ++ lc) × ℕ → Run (foldr _++_ lc ls) × ℕ
  assocRun ls lc (r , n) rewrite concat-foldr ls lc = r , n

  record rewriteRules : Set where
    field
      len-dec-rewrite : {lc : 𝕃 char} → (r : Run lc) → maybe (Run lc × ℕ) --(λ r' → length-run r' < length-run r ≡ tt))

module noderiv where

  data RunElement : Set where
    Id : string → RunElement 
    InputChar : (c : char) → RunElement 
    ParseTree : ParseTreeT → RunElement 
    Posinfo : ℕ → RunElement

  Run : Set
  Run = 𝕃 RunElement

  _::'_ : RunElement → Run → Run
  _::'_ = _::_

  []' : Run
  []' = []

  length-run : Run → ℕ
  length-run = length

  RunElement-to-string : RunElement → string
  RunElement-to-string (Id s) = ("id:" ^ s)
  RunElement-to-string (InputChar c) = "#" ^ (char-to-string c)
  RunElement-to-string (ParseTree pt) = (ParseTreeToString pt)
  RunElement-to-string (Posinfo n) = "pos:" ^ ℕ-to-string n

  Run-to-string : Run → string
  Run-to-string [] = "\n"
  Run-to-string (e :: r) =  (RunElement-to-string e) ^ " " ^ (Run-to-string r) 

  record rewriteRules : Set where
    field
      len-dec-rewrite : Run → maybe (Run × ℕ)

empty-string : string
empty-string = ""

