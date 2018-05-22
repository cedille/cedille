module constants where

open import lib

cedille-extension : string
cedille-extension = "ced"

self-name : string
self-name = "self"

ignored-var : string
ignored-var = "_"

options-file-name : string
options-file-name = "options"

global-error-string : string → string
global-error-string msg = "{\"error\":\"" ^ msg ^ "\"" ^ "}"

dot-cedille-directory : string → string 
dot-cedille-directory dir = combineFileNames dir ".cedille"
