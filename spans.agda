module spans where

open import lib
open import cedille-types 
open import to-string

tagged-val : Set
tagged-val = string × string

tagged-val-to-string : tagged-val → string
tagged-val-to-string (tag , val) = "\"" ^ tag ^ "\":\"" ^ val ^ "\""

type-data : type → tagged-val
type-data tp = "type" , type-to-string tp 

kind-data : kind → tagged-val
kind-data k = "kind" , kind-to-string k

tk-data : tk → tagged-val
tk-data (Tkk k) = kind-data k
tk-data (Tkt t) = type-data t

data span : Set where
  mk-span : string → posinfo → posinfo → 𝕃 tagged-val {- extra information for the span -} → span

span-to-string : span → string
span-to-string (mk-span name start end extra) = 
  "[\"" ^ name ^ "\"," ^ start ^ "," ^ end ^ ",{" 
        ^ string-concat-sep-map "," tagged-val-to-string extra ^ "}]"

data spans : Set where
  regular-spans : 𝕃 span → spans
  global-error : string {- error message -} → maybe span → spans

global-error-p : spans → 𝔹
global-error-p (global-error _ _) = tt
global-error-p _ = ff

empty-spans : spans
empty-spans = regular-spans []

spans-to-string : spans → string
spans-to-string (regular-spans ss) = "{\"spans\":[" ^ (string-concat-sep-map "," span-to-string ss) ^ "]}\n"
spans-to-string (global-error e o) = "{\"error\":\"" ^ e ^ helper o ^ "\"" ^ "}\n"
  where helper : maybe span → string
        helper (just x) = ", \"global-error\":" ^ span-to-string x
        helper nothing = ""

add-span : span → spans → spans
add-span s (regular-spans ss) = regular-spans (s :: ss)
add-span s (global-error e e') = global-error e e'

Rec-name : string
Rec-name = "Rec"

explain-name : string
explain-name = "explanation"

Rec-explain : string → tagged-val
Rec-explain datatype-name = (explain-name , "Definition of recursive datatype " ^ datatype-name)

Star-name : string
Star-name = "Star"

Decl-name : string
Decl-name = "Decl"
