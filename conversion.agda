module conversion where

open import lib

open import cedille-types
open import defeq
open import rename
open import syntax-util
open import subst
open import tpstate
open import lift

synthconv-t : Set → Set
synthconv-t A = (maybe A) × string -- the string is for responses to holes or errors

infixr 1 _≫synthconv_

_≫synthconv_ : {A B : Set} → synthconv-t A → (A → synthconv-t B) → synthconv-t B
nothing , m ≫synthconv f = nothing , m
just a , m ≫synthconv f with f a 
just a , m ≫synthconv f | r , m' = r , (m ^ (newline-sep-if m m') ^ m')

synthconv-errstr : evidence → term → string
synthconv-errstr e t = ("We have no matching case for converting the given term with the given evidence.\n"
                      ^ "1. the term: " ^ term-to-string t ^ "\n"
                      ^ "2. the evidence: " ^ evidence-to-string e )

{-# NO_TERMINATION_CHECK #-}
synth-conversion-type : tpstate → ctxt → evidence → type → synthconv-t type
synth-conversion-term : tpstate → ctxt → evidence → term → synthconv-t term
synth-conversion-kind : tpstate → ctxt → evidence → kind → synthconv-t kind
synth-conversion-type s Γ (Eparens e) tp = synth-conversion-type s Γ e tp 
synth-conversion-type s Γ e (TpParens tp) = synth-conversion-type s Γ e tp 
synth-conversion-type s Γ (Ehole c) tp = 
  just tp , show-evctxt-if c Γ ^ type-to-string tp ^ " ≃ ?\n"
synth-conversion-type s Γ (EholeNamed c n) tp  = 
  just tp , show-evctxt-if c Γ ^ n ^ " ∷ " ^ type-to-string tp ^ " ≃ ?\n"
synth-conversion-type s Γ Check tp = just tp , ""
synth-conversion-type s Γ (Trans e e') tp = 
  synth-conversion-type s Γ e tp ≫synthconv λ tp' → 
  synth-conversion-type s Γ e' tp'
synth-conversion-type s Γ (Eapp e1 e2) (TpApp tp1 tp2)  =
  synth-conversion-type s Γ e1 tp1 ≫synthconv λ tp1' → 
  synth-conversion-type s Γ e2 tp2 ≫synthconv λ tp2' → just (TpApp tp1' tp2') , ""
synth-conversion-type s Γ (Eapp e1 e2) (TpAppt tp trm)  =
  synth-conversion-type s Γ e1 tp ≫synthconv λ tp' → 
  synth-conversion-term s Γ e2 trm ≫synthconv λ trm' → just (TpAppt tp' trm') , ""
synth-conversion-type s (Δ , b , r) e (TpVar x) with lookup-type-var s (renamectxt-rep r x)
synth-conversion-type s (Δ , b , r) e (TpVar x) | nothing = 
  nothing , ("Synthesizing conversion encountered an undefined type variable.\n1. the type variable: " ^ x)
synth-conversion-type s (Δ , b , r) e (TpVar x) | just tp = synth-conversion-type s (Δ , b , r) e tp
synth-conversion-type s (Δ , b , r) Beta (Nu X k Θ tp) = just (type-subst-type r (rename-pred s b) (Nu X k Θ tp) X tp) , ""
synth-conversion-type s (Δ , b , r) Beta (TpApp (AbsTp2 Lambda x a tp) tp') = 
 just (type-subst-type r (rename-pred s b) tp' x tp) , ""
synth-conversion-type s (Δ , b , r) Beta (TpApp (TpParens tp) tp') = 
  synth-conversion-type s (Δ , b , r) Beta (TpApp tp tp') 
synth-conversion-type s (Δ , b , r) Beta (TpAppt (AbsTp2 Lambda x a tp) t') = 
 just (term-subst-type r (rename-pred s b) t' x tp) , ""
synth-conversion-type s (Δ , b , r) Beta (TpAppt (TpParens tp) t') = 
  synth-conversion-type s (Δ , b , r) Beta (TpAppt tp t') 
synth-conversion-type s (Δ , b , r) Beta (TpApp (TpVar x) tp') with lookup-type-var s (renamectxt-rep r x)
synth-conversion-type s (Δ , b , r) Beta (TpApp (TpVar x) tp') | nothing = nothing , ""
synth-conversion-type s (Δ , b , r) Beta (TpApp (TpVar x) tp') | just tp = synth-conversion-type s (Δ , b , r) Beta (TpApp tp tp')
synth-conversion-type s (Δ , b , r) Beta (TpAppt (TpVar x) t') with lookup-type-var s (renamectxt-rep r x)
synth-conversion-type s (Δ , b , r) Beta (TpAppt (TpVar x) t') | nothing = nothing , ""
synth-conversion-type s (Δ , b , r) Beta (TpAppt (TpVar x) t') | just tp = synth-conversion-type s (Δ , b , r) Beta (TpAppt tp t')
synth-conversion-type s (Δ , b , r) Beta (Lft x t ltp) = just (do-lift s b r x t ltp) , ""

synth-conversion-type s Γ (Earrow e1 e2) (TpArrow tp1 tp2) =
  synth-conversion-type s Γ e1 tp1 ≫synthconv λ tp1' → 
  synth-conversion-type s Γ e2 tp2 ≫synthconv λ tp2' → 
    just (TpArrow tp1' tp2') , ""
synth-conversion-type s Γ e tp = nothing , ("We have no matching case for synth-conversion-type for the given type and evidence.\n"
                                           ^ "1. the type: " ^ type-to-string tp ^ "\n"
                                           ^ "2. the evidence: " ^ evidence-to-string e)

synth-conversion-term s Γ e (Parens t) = synth-conversion-term s Γ e t
synth-conversion-term s Γ (Eparens e) t = synth-conversion-term s Γ e t
synth-conversion-term s (Δ , b , r) Beta (App (Lam x t) t') = 
  just (term-subst-term r (rename-pred s b) t' x t) , ""
synth-conversion-term s Γ Beta (App (Var x) t') with lookup-term-var s x
synth-conversion-term s Γ Beta (App (Var x) t') | nothing = nothing , synthconv-errstr Beta (App (Var x) t') 
synth-conversion-term s Γ Beta (App (Var x) t') | just trm = synth-conversion-term s Γ Beta (App trm t')
synth-conversion-term s Γ (Eapp e1 e2) (App t1 t2) = 
  synth-conversion-term s Γ e1 t1 ≫synthconv λ t1' → 
  synth-conversion-term s Γ e2 t2 ≫synthconv λ t2' → 
   just (App t1' t2') , ""
synth-conversion-term s Γ Check t = just t , ""
synth-conversion-term s Γ e t2 = nothing , synthconv-errstr e t2

synth-conversion-kind s (Δ , b , r) e k = nothing , "unimplemented part of synth-conversion-kind"