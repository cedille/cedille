module syntax-util where

open import lib
open import cedille-types

posinfo-gen : posinfo
posinfo-gen = "generated"

posinfo-to-ℕ : posinfo → ℕ
posinfo-to-ℕ pi with string-to-ℕ pi
posinfo-to-ℕ pi | just n = n
posinfo-to-ℕ pi | nothing = 0 -- should not happen

tk-is-type : tk → 𝔹
tk-is-type (Tkt _) = tt
tk-is-type (Tkk _) = ff

indices-to-decls : indices → decls
indices-to-decls Indicese = DeclsNil
indices-to-decls (Indicesne x) = x

decls-pi-bind-kind : decls → kind → kind
decls-pi-bind-kind DeclsNil k = k
decls-pi-bind-kind (DeclsCons (Decl _ x atk _) ds) k = KndPi x atk (decls-pi-bind-kind ds k)

