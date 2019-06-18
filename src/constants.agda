module constants where

open import general-util

cedille-extension : string
cedille-extension = "ced"

cdle-extension : string
cdle-extension = "cdle"

self-name : string
self-name = "self"

delimiter = '§'

pattern ignored-var = "_"

pattern meta-var-pfx = '?'
pattern qual-local-chr = '@'
pattern qual-global-chr = '.'

meta-var-pfx-str = 𝕃char-to-string [ meta-var-pfx ]
qual-local-str = 𝕃char-to-string [ qual-local-chr ]
qual-global-str = 𝕃char-to-string [ qual-global-chr ]

options-file-name : string
options-file-name = "options"

global-error-string : string → string
global-error-string msg = "{\"error\":\"" ^ msg ^ "\"" ^ "}"

dot-cedille-directory : string → string 
dot-cedille-directory dir = combineFileNames dir ".cedille"

pattern elab-mu-prev-key = "/prev"
pattern elab-hide-key = "/hide"
