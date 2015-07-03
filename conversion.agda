module conversion where

open import lib

open import cedille-types
open import check-util
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
convert-type ct s Γ (EliftCong e) (Lft trm ltp) = 
  convert-term ct s Γ e trm ≫conv λ trm' → just (Lft trm' ltp) , ""
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
convert-type ct s (Δ , b , r) Beta (Lft t ltp) = just (do-lift s b r t ltp) , ""
convert-type ct s (Δ , b , r) (EtaLift nstr) (Lft t ltp) with string-to-ℕ nstr
convert-type ct s (Δ , b , r) (EtaLift nstr) (Lft t ltp) | nothing =
  nothing , "Internal error converting a string to a natural number for eta lift (should not happen)."
convert-type ct s (Δ , b , r) (EtaLift nstr) (Lft t ltp) | just n = hl n t [] 
  where hl : ℕ → term → 𝕃 var → conv-t type
        ha : term → 𝕃 var → conv-t type
        hl n (Parens t) vs = hl n t vs
        hl (suc n) (Lam x t) vs = hl n t (x :: vs)
        hl 0 t vs = ha t vs
        hl n t vs = nothing , ("Conversion using eta for lift types (η↑) could not find " ^ nstr 
                              ^ "lambda-abstractions to try to eta-contract.\n"
                              ^ "1. the term we encountered after fewer than " ^ nstr ^ " lambda abstractions: " ^ term-to-string t)
 
        ha (Parens t) vs = ha t vs
        ha (App t1 (Parens t2)) vs = ha (App t1 t2) vs  
        ha (App t1 (Var y)) (y' :: vs) = 
          if y =string y' then ha t1 vs 
          else (nothing , ("Conversion using eta for lift types (η↑) failed matching bound and applied variables.\n"
                         ^ "1. the bound variable: " ^ y' ^ "\n"
                         ^ "2. the applied variable in the body of the lambda-abstraction to be eta-contracted: " ^ y))
        ha t [] = just (Lft t ltp) , ""
        ha t vs = nothing , ("Conversion using eta for lift types (η↑) could not find " ^ nstr ^ " nested applications to variables\n"
                           ^ "in the body of the lambda abstraction to be eta-contracted.\n"
                           ^ "1. the term where we got stuck: " ^ term-to-string t)
         
convert-type ct s (Δ , b , r) (RbetaLift nstr) (TpApp tp1 tp2) with string-to-ℕ nstr
convert-type ct s (Δ , b , r) (RbetaLift nstr) (TpApp tp1 tp2) | nothing =
  nothing , "Internal error converting a string to a natural number for rbeta lift (should not happen)."
convert-type ct s (Δ , b , r) (RbetaLift nstr) (TpApp tp1 tp2) | just n with remove-type-args n tp1 | remove-type-args n tp2
convert-type ct s (Δ , b , r) (RbetaLift nstr) (TpApp tp1 tp2) | just n | nothing | x = 
  nothing , (convert-type-rbeta-lift-err nstr tp1)
convert-type ct s (Δ , b , r) (RbetaLift nstr) (TpApp tp1 tp2) | just n | just (h1 , args1) | nothing = 
  nothing , (convert-type-rbeta-lift-err nstr tp2)
convert-type ct s (Δ , b , r) (RbetaLift nstr) (TpApp tp1 tp2) | just n | just (Lft h1 ltp1 , args1) | just (Lft h2 ltp2 , args2) = 
  if eq-types s (bctxt-contains b) r args1 args2 then
    (h (remove-lam-vars n h1) (remove-lam-vars n h2) (remove-inputs-liftingType n ltp1))
  else
    (nothing , ("Trying to do an rbeta-lift conversion, we did not extract " ^ nstr ^ " equal arguments from both types.\n"
             ^ "1. the first type: " ^ type-to-string tp1 ^ "\n"  
             ^ "2. the second type: " ^ type-to-string tp2))
  where h : {n : ℕ} → maybe ((𝕍 string n) × term) → maybe ((𝕍 string n) × term) → maybe ((𝕍 liftingType n) × liftingType) → conv-t type
        h nothing x y = nothing , ("Trying to do an rbeta-lift conversion, we could not extract " ^ nstr
                               ^ " lambda-abstractions beneath a lift type.\n1. the type: " ^ type-to-string (Lft h1 ltp1))
        h (just (vs1 , b1)) nothing y = nothing , ("Trying to do an rbeta-lift conversion, we could not extract " ^ nstr
                                              ^ " lambda-abstractions beneath a lift type.\n1. the type: " ^ type-to-string (Lft h2 ltp2))
        h (just (vs1 , b1)) (just (vs2 , b2)) (just (ins , LiftArrow _ ltpr)) = 
          just 
            (type-app-spine 
              (Lft (lambdas (𝕍-to-𝕃 vs1)
                     (App b1 (rename-term (renamectxt-insert* empty-renamectxt vs2 vs1) (bctxt-contains b) b2)))
                   (lift-arrows (𝕍-to-𝕃 ins) ltpr))
              (reverse (𝕍-to-𝕃 args1))) , ""
        h (just (vs1 , b1)) (just (vs2 , b2)) x = 
          nothing , ("Trying to do an rbeta-lift conversion, we could not extract " ^ nstr
                   ^ " domain types from around an arrow lifting type (should not happen?).\n"
                   ^ "1. the lifting type: " ^ liftingType-to-string ltp1)
convert-type ct s (Δ , b , r) (RbetaLift nstr) (TpApp tp1 tp2) | just n | just (h1 , args1) | just (h2 , args2) = 
   nothing , ("Trying to do an rbeta-lift conversion, the remaining head of one of the types is not a lift type.\n"
            ^ "1. the remaining head of the first type: " ^ type-to-string h1 ^ "\n"
            ^ "2. the remaining head of the second type: " ^ type-to-string h2)

convert-type ct s (Δ , b , r) (EtaAll e t) (AbsTp2 All x (Tkt tp1) tp2) =
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

convert-type ct s Γ e tp = nothing , ("We have no matching case for converting the given type with the given evidence.\n"
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
convert-term ct s (Δ , b , r) (LamCong e) (Lam x trm) =
    let x' = rename-away s b r x in
    convert-term ct s (Δ , bctxt-add b x' , renamectxt-insert r x x') e trm ≫conv λ trm' → 
      just (Lam x' trm') , ""

convert-term ct s Γ e t2 = nothing , conv-errstr e t2


convert-kind ct s (Δ , b , r) e k = nothing , "Kind-level conversion is unimplemented."

convert-tk ct s Γ e (Tkt t) = (convert-type ct s Γ e t) ≫conv λ t' → just (Tkt t') , ""
convert-tk ct s Γ e (Tkk k) = (convert-kind ct s Γ e k) ≫conv λ k' → just (Tkk k') , ""