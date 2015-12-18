module spans where

open import lib
open import cedille-types 

tagged-val : Set
tagged-val = string × string

tagged-val-to-string : tagged-val → string
tagged-val-to-string (tag , val) = tag ^ ":" ^ val

type-data : type → tagged-val
type-data tp = "\"type\"" , "\"" ^ type-to-string tp ^ "\""

data span : Set where
  mk-span : string → posinfo → posinfo → 𝕃 tagged-val {- extra information for the span -} → span

span-to-string : span → string
span-to-string (mk-span name start end extra) = 
  "[\"" ^ name ^ "\"," ^ start ^ "," ^ end ^ ",{" 
        ^ string-concat-sep-map "," tagged-val-to-string extra ^ "}]"


spans-to-string : 𝕃 span → string
spans-to-string = string-concat-sep-map "," span-to-string 
