module hnf-tests where

open import bool
open import list
open import nat
open import product 
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

try-pull-lift-types : type → type → type
try-pull-lift-types tp1 tp2 with decompose-tpapps tp1 | decompose-tpapps (hnf new-ctxt unfold-head tp2)
try-pull-lift-types tp1 tp2 | Lft _ _ X t l , args1 | Lft _ _ X' t' l' , args2 =
   if conv-tty* new-ctxt args1 args2 then
      try-pull-term-in t l (length args1) [] []
   else
      TpApp tp1 tp2
   where try-pull-term-in : term → liftingType → ℕ → 𝕃 var → 𝕃 liftingType → type
         try-pull-term-in t (LiftParens _ l _) n vars ltps = try-pull-term-in t l n vars ltps 
         try-pull-term-in t (LiftArrow _ l) 0 vars ltps = 
           recompose-tpapps 
             (Lft posinfo-gen posinfo-gen X (Lam* vars (hnf Γ no-unfolding (App t NotErased (App* t' (map mvar vars)))))
               (LiftArrow* ltps l) , args1)
         try-pull-term-in (Lam _ _ _ x _ t) (LiftArrow l1 l2) (suc n) vars ltps =
           try-pull-term-in t l2 n (x :: vars) (l1 :: ltps) 
         try-pull-term-in t (LiftArrow l1 l2) (suc n) vars ltps =
           let x = fresh-var "x" (ctxt-binds-var Γ) empty-renamectxt in
             try-pull-term-in (App t NotErased (mvar x)) l2 n (x :: vars) (l1 :: ltps) 
         try-pull-term-in t l n vars ltps = TpApp tp1 tp2

try-pull-lift-types tp1 tp2 | h , a | h' , a' = TpApp tp1 tp2


lta = (TpApp (Lft posinfo-gen posinfo-gen "X" (mvar "f") 
               (LiftArrow (LiftStar posinfo-gen) (LiftArrow (LiftStar posinfo-gen) (LiftStar posinfo-gen))))
             (mtpvar "doit"))
ltb = (TpApp (Lft posinfo-gen posinfo-gen "X" (mvar "t") (LiftStar posinfo-gen)) (mtpvar "doit"))

lt = try-pull-lift-types lta ltb

lts = to-string lt
