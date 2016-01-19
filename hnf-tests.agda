module hnf-tests where

open import bool
open import string

open import cedille-types
open import conversion
open import ctxt
open import is-free
open import rename
open import subst
open import syntax-util
open import to-string

S : term
S = mlam "n" (mlam "s" (mlam "z" (mapp (mvar "s") (mapp (mapp (mvar "n") (mvar "s")) (mvar "z")))))

plus : term
plus = mlam "n" (mlam "m" (mapp (mapp (mvar "n") S) (mvar "m")))

zero : term
zero = mlam "s" (mlam "z" (mvar "z"))

one : term
one = mlam "s" (mlam "z" (mapp (mvar "s") (mvar "z")))

plus-one-zero : term
plus-one-zero = mapp (mapp plus one) zero

run : term → term
run t = hnf new-ctxt unfold-head t 

show : term → string
show t = term-to-string t

s2 = show (run (mapp S (mvar "z")))

-- λ s . (λ x . λ s . x λ s' . f s' s) s 

t1 = mlam "s" (mapp (mlam "x" (mlam "s" (mapp (mvar "x") (mlam "s'" (mapp (mapp (mvar "f") (mvar "s'")) (mvar "s")))))) (mvar "s"))

s1 = show (run t1)

Γ = ctxt-var-decl "s" new-ctxt

q = show (subst-term Γ (mvar "s") "x" (mlam "s" (mapp (mvar "x") (mlam "s'" (mapp (mapp (mvar "f") (mvar "s'")) (mvar "s"))))))

r = show (subst-term Γ (mvar "s") "x" (mlam "s" (mlam "s'" (mapp (mapp (mvar "f") (mvar "s'")) (mvar "s")))))

aa = rename-var-if Γ empty-renamectxt "s" (mvar "s")

Γ' = ctxt-var-decl "s'" Γ
ρ = renamectxt-insert empty-renamectxt "s" "s'"

bb = show (substh-term Γ' ρ (mvar "s") "x" (mlam "s'" (mapp (mapp (mvar "f") (mvar "s'")) (mvar "s"))))

cc = rename-var-if Γ' ρ "s'" (mvar "s")
