module conversion where

open import lib

open import cedille-types
open import defeq
open import free
open import lift
open import rename
open import syntax-util
open import subst
open import tpstate

conv-errstr : evidence → term → string
conv-errstr e t = ("We have no matching case for converting the given term with the given evidence.\n"
                      ^ "1. the term: " ^ term-to-string t ^ "\n"
                      ^ "2. the evidence: " ^ evidence-to-string e )


{-# NO_TERMINATION_CHECK #-}

convert-type : check-term-t → tpstate → ctxt → evidence → type → conv-t type
convert-term : check-term-t → tpstate → ctxt → evidence → term → conv-t term
convert-kind : check-term-t → tpstate → ctxt → evidence → kind → conv-t kind
convert-tk : check-term-t → tpstate → ctxt → evidence → tk → conv-t tk

convert-type ct s Γ (Eparens e) tp = convert-type ct s Γ e tp 
convert-type ct s Γ e (TpParens tp) = convert-type ct s Γ e tp 
convert-type ct s Γ (Ehole c) tp = 
  just tp , show-evctxt-if c Γ ^ type-to-string tp ^ " ≃ ?\n"
convert-type ct s Γ (EholeNamed c n) tp  = 
  just tp , show-evctxt-if c Γ ^ n ^ " ∷ " ^ type-to-string tp ^ " ≃ ?\n"
convert-type ct s Γ Check tp = just tp , ""
convert-type ct s Γ (Trans e e') tp = 
  convert-type ct s Γ e tp ≫conv λ tp' → 
  convert-type ct s Γ e' tp'
convert-type ct s Γ (Eapp e1 e2) (TpApp tp1 tp2)  =
  convert-type ct s Γ e1 tp1 ≫conv λ tp1' → 
  convert-type ct s Γ e2 tp2 ≫conv λ tp2' → just (TpApp tp1' tp2') , ""
convert-type ct s Γ (Eapp e1 e2) (TpAppt tp trm)  =
  convert-type ct s Γ e1 tp ≫conv λ tp' → 
  convert-term ct s Γ e2 trm ≫conv λ trm' → just (TpAppt tp' trm') , ""
convert-type ct s (Δ , b , r) e (TpVar x) with lookup-type-var s (renamectxt-rep r x)
convert-type ct s (Δ , b , r) e (TpVar x) | nothing = 
  nothing , ("Synthesizing conversion encountered an undefined type variable.\n1. the type variable: " ^ x)
convert-type ct s (Δ , b , r) e (TpVar x) | just tp = convert-type ct s (Δ , b , r) e tp
convert-type ct s (Δ , b , r) Beta (Nu X k Θ tp) = just (type-subst-type r (rename-pred s b) (Nu X k Θ tp) X tp) , ""
convert-type ct s (Δ , b , r) Beta (TpApp (AbsTp2 Lambda x a tp) tp') = 
 just (type-subst-type r (rename-pred s b) tp' x tp) , ""
convert-type ct s (Δ , b , r) Beta (TpApp (TpParens tp) tp') = 
  convert-type ct s (Δ , b , r) Beta (TpApp tp tp') 
convert-type ct s (Δ , b , r) Beta (TpAppt (AbsTp2 Lambda x a tp) t') = 
 just (term-subst-type r (rename-pred s b) t' x tp) , ""
convert-type ct s (Δ , b , r) Beta (TpAppt (TpParens tp) t') = 
  convert-type ct s (Δ , b , r) Beta (TpAppt tp t') 
convert-type ct s (Δ , b , r) Beta (TpApp (TpVar x) tp') with lookup-type-var s (renamectxt-rep r x)
convert-type ct s (Δ , b , r) Beta (TpApp (TpVar x) tp') | nothing = nothing , ""
convert-type ct s (Δ , b , r) Beta (TpApp (TpVar x) tp') | just tp = convert-type ct s (Δ , b , r) Beta (TpApp tp tp')
convert-type ct s (Δ , b , r) Beta (TpAppt (TpVar x) t') with lookup-type-var s (renamectxt-rep r x)
convert-type ct s (Δ , b , r) Beta (TpAppt (TpVar x) t') | nothing = nothing , ""
convert-type ct s (Δ , b , r) Beta (TpAppt (TpVar x) t') | just tp = convert-type ct s (Δ , b , r) Beta (TpAppt tp t')
convert-type ct s (Δ , b , r) Beta (Lft x t ltp) = just (do-lift s b r x t ltp) , ""
convert-type ct s (Δ , b , r) (Eta e t) (AbsTp2 All x (Tkt tp1) tp2) =
  (ct s (Δ , b , r) e t tp1) ≫checkconv
  (if type-var-free-in-type s b r x tp2 then 
   (nothing , ("Conversion has received a request to drop a vacuous type-level universal quantification over types,\n"
            ^ "but the quantified variable is used in the body.\n"
            ^ "1. the type in question: " ^ type-to-string (AbsTp2 All x (Tkt tp1) tp2)))
  else (just tp2 , ""))

convert-type ct s Γ (Earrow e1 e2) (TpArrow tp1 tp2) =
  convert-type ct s Γ e1 tp1 ≫conv λ tp1' → 
  convert-type ct s Γ e2 tp2 ≫conv λ tp2' → 
    just (TpArrow tp1' tp2') , ""

convert-type ct s (Δ , b , r) (Xi u (EclassSome e1) e2) (AbsTp2 o x a tp) =
  convert-tk ct s (Δ , b , r) e1 a ≫conv λ a' → 
    let x' = rename-away s b r x in
    convert-type ct s (evctxt-insert-tk Δ u x' a' , bctxt-add b x' , renamectxt-insert r x x') e2 tp ≫conv λ tp' → 
      just (AbsTp2 o x' a' tp') , ""

convert-type ct s (Δ , b , r) (Xi u EclassNone e2) (AbsTp2 o x a tp) =
    let x' = rename-away s b r x in
    convert-type ct s (evctxt-insert-tk Δ u x' a , bctxt-add b x' , renamectxt-insert r x x') e2 tp ≫conv λ tp' → 
      just (AbsTp2 o x' a tp') , ""

convert-type ct s Γ e tp = nothing , ("We have no matching case for convert-type ct for the given type and evidence.\n"
                                           ^ "1. the type: " ^ type-to-string tp ^ "\n"
                                           ^ "2. the evidence: " ^ evidence-to-string e)

convert-term ct s Γ e (Parens t) = convert-term ct s Γ e t
convert-term ct s Γ (Eparens e) t = convert-term ct s Γ e t
convert-term ct s (Δ , b , r) Beta (App (Lam x t) t') = 
  just (term-subst-term r (rename-pred s b) t' x t) , ""
convert-term ct s Γ Beta (App (Var x) t') with lookup-term-var s x
convert-term ct s Γ Beta (App (Var x) t') | nothing = nothing , conv-errstr Beta (App (Var x) t') 
convert-term ct s Γ Beta (App (Var x) t') | just trm = convert-term ct s Γ Beta (App trm t')
convert-term ct s Γ (Eapp e1 e2) (App t1 t2) = 
  convert-term ct s Γ e1 t1 ≫conv λ t1' → 
  convert-term ct s Γ e2 t2 ≫conv λ t2' → 
   just (App t1' t2') , ""
convert-term ct s Γ Check t = just t , ""
convert-term ct s Γ e t2 = nothing , conv-errstr e t2

convert-kind ct s (Δ , b , r) e k = nothing , "unimplemented part of convert-kind ct"

convert-tk ct s Γ e (Tkt t) = (convert-type ct s Γ e t) ≫conv λ t' → just (Tkt t') , ""
convert-tk ct s Γ e (Tkk k) = (convert-kind ct s Γ e k) ≫conv λ k' → just (Tkk k') , ""