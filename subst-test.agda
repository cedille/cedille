module subst-test where

open import lib
open import cedille-types
open import rename
open import subst

test-subst1 : term
test-subst1 = term-subst-term empty-renamectxt (_=string_ "f") (Var "f") "f" (Lam "f" (Var "f"))

test-subst2 : term
test-subst2 = term-subst-term (renamectxt-insert empty-renamectxt "f" "f'") (_=string_ "f") (Var "g") "f" (Var "f")

test-subst3 : term
test-subst3 = term-subst-term empty-renamectxt (λ x → ff) (Var "g") "f" (Lam "f" (Var "f"))