module conversion where

open import lib

open import cedille-types
open import defeq
open import rename
open import syntax-util
open import subst
open import tpstate

infixr 1 _≫conv_ 

conv-t : Set
conv-t = 𝔹 × string -- the string is for responses to holes

_≫conv_ : conv-t → conv-t → conv-t
(b1 , m1) ≫conv (b2 , m2) = (b1 && b2 , m1 ^ "\n" ^ m2)

check-conversion-type : tpstate → ctxt → evidence → type → type → conv-t
check-conversion-term : tpstate → ctxt → evidence → term → term → conv-t
check-conversion-type s Γ e (TpParens tp) tp' = check-conversion-type s Γ e tp tp' 
check-conversion-type s Γ e tp (TpParens tp') = check-conversion-type s Γ e tp tp' 
check-conversion-type s Γ (Ehole c) tp tp' = 
  (tt , show-evctxt-if c Γ ^ type-to-string tp ^ " ≃ " ^ type-to-string tp' ^ "\n")
check-conversion-type s Γ (EholeNamed c n) tp tp' = 
  (tt , show-evctxt-if c Γ ^ n ^ " ∷ " ^ type-to-string tp ^ " ≃ " ^ type-to-string tp' ^ "\n")
check-conversion-type s Γ (Eapp e1 e2) (TpApp tp1 tp2) (TpApp tp1' tp2') =
  check-conversion-type s Γ e1 tp1 tp1' ≫conv check-conversion-type s Γ e2 tp2 tp2'
check-conversion-type s Γ (Eapp e1 e2) (TpAppt tp trm) (TpAppt tp' trm') =
  check-conversion-type s Γ e1 tp tp' ≫conv check-conversion-term s Γ e2 trm trm'
check-conversion-type s (Δ , b , r) Check tp tp' = eq-type s (rename-pred s b) r tp tp' , ""
check-conversion-type s Γ e tp tp' = ff , "unimplemented part of check-conversion-type"

check-conversion-term s (Δ , b , r) Beta (App (Lam x t) t') t2 = 
  if eq-term s (bctxt-contains b) r t2 (term-subst-term r (rename-pred s b) t' x t) then
     (tt , "")
  else
     (ff , ("While checking conversion, a beta-reduction does not result in the expected term.\n\n"
          ^ "1. the beta-redex: " ^ term-to-string (App (Lam x t) t') ^ "\n"
          ^ "2. the expected term: " ^ term-to-string t2))
check-conversion-term s (Δ , b , r) e t2 t2' = ff , "unimplemented part of check-conversion-term"
