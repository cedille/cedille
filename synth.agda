module synth where

open import lib

open import cedille-types
open import check-util
open import check
open import conversion
open import defeq
open import free
open import lift
open import rename
open import syntax-util
open import subst
open import tpstate

{-# NO_TERMINATION_CHECK #-}
synth-type : synth-type-t
try-synth-type : try-synth-type-t

synth-term : synth-term-t
try-synth-term : try-synth-term-t

synth-funcs : s-t

synth-type s Γ (Eparens e) t = synth-type s Γ e t
synth-type s Γ e (TpParens t) = synth-type s Γ e t
synth-type s Γ (Eprint c e) t = 
  synth-type s Γ e t ≫synth λ k → 
  no-error ((show-evctxt-if c Γ ^ type-to-string t ^ " ⇒ " ^ kind-to-string k ^ "\n") , k)
synth-type s Γ (Ehole _) t = holewrong-type t
synth-type s Γ (EholeNamed _ _) t = holewrong-type t
synth-type s Γ (Elet d e') t = check-defh (mk-s synth-type try-synth-type synth-term try-synth-term) s Γ d ≫=err λ s' →
                               synth-type s' Γ e' t

synth-type s (Δ , b , r) (Evar u) t with evctxt-lookup Δ u 
synth-type s (Δ , b , r) (Evar u) t | nothing with lookup-type-var-tk s u 
synth-type s (Δ , b , r) (Evar u) t | nothing | nothing =
  yes-error ("An evidence variable was found to be undeclared while attempting to synthesize a kind.\n"
           ^ "1. the evidence variable: " ^ u ^ "\n"
           ^ "2. " ^ synth-type-errstr t)
synth-type s (Δ , b , r) (Evar u) t | nothing | just (t' , k) = 
  if eq-type s (bctxt-contains b) r t t' then (no-error ("" , k)) 
  else (yes-error ("An evidence variable proves a kinding for a different type than the one we are trying to kind.\n"
                 ^ "1. the evidence variable: " ^ u ^ "\n"
                 ^ "2. the kinding it proves: " ^ type-to-string t' ^ " ∷ " ^ kind-to-string k ^ "\n"
                 ^ "3. the type we are trying to kind: " ^ type-to-string t))
synth-type s (Δ , b , r) (Evar u) t | just (term-type trm tp) = 
  yes-error ("An evidence variable proving a typing is being used to try to synthesize a kind.\n"
           ^ "1. the evidence variable: " ^ u ^ " ∷ " ^ term-to-string trm ^ " : " ^ type-to-string tp ^ "\n"
           ^ "2. " ^ synth-type-errstr t)
synth-type s (Δ , b , r) (Evar u) t | just (type-kind t' k) with eq-type s (bctxt-contains b) r t' t
synth-type s (Δ , b , r) (Evar u) t | just (type-kind t' k) | tt = no-error ("" , k)
synth-type s (Δ , b , r) (Evar u) t | just (type-kind t' k) | ff = 
  yes-error ("An evidence variable is being used to try to synthesize a kind, but that variable proves a different kinding.\n"
           ^ "1. the evidence variable: " ^ u ^ " ∷ " ^ type-to-string t' ^ " : " ^ kind-to-string k ^ "\n"
           ^ "2. " ^ synth-type-errstr t)
synth-type s (Δ , b , r) (Evar u) t | just (ev-ctorset Θ) = 
  yes-error ("An evidence variable proving a ctor set is being used to try to synthesize a kind.\n"
           ^ "1. the evidence variable: " ^ u ^ " ∷ " ^ ctorset-to-string Θ ^ "\n"
           ^ "2. " ^ synth-type-errstr t)

synth-type s (Δ , b , r) (Eapp e e') (TpApp t t') = synth-type s (Δ , b , r) e t ≫synth h 
  where h : kind → synth-t kind
        h (KndParens k) = h k
        h (KndArrow k1 k2) = 
          check-type (mk-s synth-type try-synth-type synth-term try-synth-term) s (Δ , b , r) e' t' k1 ≫checksynth 
          no-error ("" , k2) 
        h (KndPi x (Tkk k1) k2) = 
          check-type (mk-s synth-type try-synth-type synth-term try-synth-term) s (Δ , b , r) e' t' k1 ≫checksynth
          no-error ("" , type-subst-kind r (rename-pred s b) t' x k2) 

        h (KndVar x) with lookup-kind-var s (renamectxt-rep r x )
        h (KndVar x) | nothing =
          yes-error ("An undeclared kind variable was synthesized for the first part of a type-level application.\n"
                   ^ "1. the first part of the application: " ^ type-to-string t ^ "\n"
                   ^ "2. the synthesized kind variable: " ^ x)
        h (KndVar x) | just k' = h k'
        h k = yes-error ("We synthesized a non-functional kind for the first part of a type-level application to a type.\n"
                       ^ "1. the first part of the application: " ^ type-to-string t ^ "\n"
                       ^ "2. the synthesized kind: " ^ kind-to-string k)

synth-type s (Δ , b , r) (Eapp e e') (TpAppt t t') = synth-type s (Δ , b , r) e t ≫synth h 
  where h : kind → synth-t kind
        h (KndParens k) = h k
        h (KndTpArrow tp k) = 
          check-term (mk-s synth-type try-synth-type synth-term try-synth-term) s (Δ , b , r) e' t' tp ≫checksynth 
          no-error ("" , k) 
        h (KndPi x (Tkt tp) k) = 
          check-term (mk-s synth-type try-synth-type synth-term try-synth-term) s (Δ , b , r) e' t' tp ≫checksynth 
          no-error ("" , term-subst-kind r (rename-pred s b) t' x k) 

        h (KndVar x) with lookup-kind-var s (renamectxt-rep r x )
        h (KndVar x) | nothing =
          yes-error ("An undeclared kind variable was synthesized for the first part of a type-level application.\n"
                   ^ "1. the first part of the application: " ^ type-to-string t ^ "\n"
                   ^ "2. the synthesized kind variable: " ^ x)
        h (KndVar x) | just k' = h k'
        h k = yes-error ("We synthesized a non-functional kind for the first part of a type-level application to a term.\n"
                       ^ "1. the first part of the application: " ^ type-to-string t ^ "\n"
                       ^ "2. the synthesized kind: " ^ kind-to-string k)

synth-type s (Δ , b , r) (Elift u e e') (Lft trm ltp) = 
  let u' : var
      u' = rename-away s b r u in
  let tp : type
      tp = liftingType-to-type u' ltp in
  let Γ' : ctxt
      Γ' = (evctxt-insert-kinding Δ u (TpVar u') Star , bctxt-add b u' , r) in
    (check-type (mk-s synth-type try-synth-type synth-term try-synth-term) s Γ' e' tp Star ≫check 
     check-term (mk-s synth-type try-synth-type synth-term try-synth-term) s Γ' e trm tp)
    ≫checksynth no-error ("" , lift-to-kind s b r ltp)

synth-type s Γ e t = 
  yes-error ("We have no matching case for synthesizing a kind for the given type, with the given evidence.\n"
            ^ "1. the type: " ^ type-to-string t ^ "\n"
            ^ "2. the evidence: " ^ evidence-to-string e)


try-synth-type s (Δ , b , r) e t k = 
  synth-type s (Δ , b , r) e t ≫synthcheck λ k' → 
  if eq-kind s (bctxt-contains b) r k k' then no-error "" 
  else (yes-error ("While trying to check a type against a kind, a different kind was synthesized.\n"
                ^ "1. the type we are checking: " ^ type-to-string t ^ "\n"
                ^ "2. the kind we synthesized for it: " ^ kind-to-string k' ^ "\n"
                ^ "3. the kind we are checking against: " ^ kind-to-string k))
  
synth-term s Γ (Eparens e) trm = synth-term s Γ e trm
synth-term s Γ e (Parens trm) = synth-term s Γ e trm
synth-term s Γ (Eprint c e) trm = 
  synth-term s Γ e trm ≫synth λ tp →
  no-error ((show-evctxt-if c Γ ^ term-to-string trm ^ " ⇒ " ^ type-to-string tp ^ "\n") , tp)
synth-term s Γ (Ehole _) trm = holewrong-term trm
synth-term s Γ (EholeNamed _ _) trm = holewrong-term trm
synth-term s Γ (Elet d e) trm = check-defh (mk-s synth-type try-synth-type synth-term try-synth-term) s Γ d ≫=err λ s' → 
                                synth-term s' Γ e trm

synth-term s (Δ , b , r) (Evar u) t with evctxt-lookup Δ u 
synth-term s (Δ , b , r) (Evar u) t | nothing with eq-term s (bctxt-contains b) r (Var u) t 
synth-term s (Δ , b , r) (Evar u) t | nothing | ff =
  yes-error ("An evidence variable could not be seen to be suitable while attempting to synthesize a type.\n"
           ^ "1. the evidence variable: " ^ u ^ "\n"
           ^ "2. " ^ synth-term-errstr t)
synth-term s (Δ , b , r) (Evar u) t | nothing | tt with lookup-term-var-t s u 
synth-term s (Δ , b , r) (Evar u) t | nothing | tt | nothing = 
  yes-error ("An evidence variable was found to be undeclared while attempting to synthesize a type.\n"
           ^ "1. the evidence variable: " ^ u ^ "\n"
           ^ "2. " ^ synth-term-errstr t)
synth-term s (Δ , b , r) (Evar u) t | nothing | tt | just tp = no-error ("" , tp)

synth-term s (Δ , b , r) (Evar u) t | just (term-type trm tp) with eq-term s (bctxt-contains b) r t trm
synth-term s (Δ , b , r) (Evar u) t | just (term-type trm tp) | tt = no-error ("" , tp)
synth-term s (Δ , b , r) (Evar u) t | just (term-type trm tp) | ff = 
  yes-error ("An evidence variable is being used to try to synthesize a type, but that variable proves a different typing.\n"
           ^ "1. the evidence variable: " ^ u ^ " ∷ " ^ term-to-string trm ^ " : " ^ type-to-string tp ^ "\n"
           ^ "2. " ^ synth-term-errstr t)
synth-term s (Δ , b , r) (Evar u) t | just (type-kind t' k) =
  yes-error ("An evidence variable proving a kinding is being used to try to synthesize a type.\n"
           ^ "1. the evidence variable: " ^ u ^ " ∷ " ^ type-to-string t' ^ " : " ^ kind-to-string k ^ "\n"
           ^ "2. " ^ synth-term-errstr t)
synth-term s (Δ , b , r) (Evar u) t | just (ev-ctorset Θ) with ctorset-find-term s (Δ , b , r) t Θ
synth-term s (Δ , b , r) (Evar u) t | just (ev-ctorset Θ) | nothing = 
  yes-error ("An evidence variable proving a ctor set is being used to synthesize a type from a term,\n"
           ^ "but the term in question is not constrained in that ctor set.\n"
           ^ "1. " ^ synth-term-errstr t ^ "\n"
           ^ "2. the evidence variable: " ^ u ^ "\n"
           ^ "3. the ctor set the evidence variable proves: " ^ ctorset-to-string Θ)
synth-term s (Δ , b , r) (Evar u) t | just (ev-ctorset Θ) | just tp = no-error ("" , tp)

synth-term s Γ (Cast e synthCast e') t =
  synth-term s Γ e t ≫synth h
  where h : type → synth-t type
        h tp with convert-type (check-term synth-funcs) s Γ e' tp 
        h tp | just tp' , m = no-error (m , tp')
        h tp | nothing , m = yes-error m 

synth-term s (Δ , b , r) (Eapp e (Eappt e' t')) t =
  synth-term s (Δ , b , r) e t ≫synth h 
  where h : type → synth-t type
        h (TpParens tp) = h tp 
        h (AbsTp2 All x (Tkt tp) tp2) = 
          check-term synth-funcs s (Δ , b , r) e' t' tp ≫checksynth 
          no-error ("" , term-subst-type r (rename-pred s b) t' x tp2) 
        h (TpVar x) with lookup-type-var s (renamectxt-rep r x )
        h (TpVar x) | nothing =
          yes-error ("An undeclared type variable was synthesized for the first part of an instantiation.\n"
                   ^ "1. the first part of the instantiation " ^ term-to-string t ^ "\n"
                   ^ "2. the synthesized type variable: " ^ x)
        h (TpVar x) | just tp' = h tp'
        h tp = yes-error ("We do not have a matching case for the instantiation value and synthesized type"
                         ^ " for an instantation.\n"
                       ^ "1. the first part of the instantiation " ^ term-to-string t ^ "\n"
                       ^ "2. the synthesized type: " ^ type-to-string tp ^ "\n"
                       ^ "3. the instantiation value: " ^ term-to-string t')

synth-term s (Δ , b , r) (Eapp e (Eappk e' tp)) t =
  synth-term s (Δ , b , r) e t ≫synth h 
  where h : type → synth-t type
        h (TpParens tp) = h tp 
        h (AbsTp2 All x (Tkk k) tp2) = 
          check-type synth-funcs s (Δ , b , r) e' tp k ≫checksynth
          no-error ("" , type-subst-type r (rename-pred s b) tp x tp2) 
        h (TpVar x) with lookup-type-var s (renamectxt-rep r x )
        h (TpVar x) | nothing =
          yes-error ("An undeclared type variable was synthesized for the first part of an instantiation.\n"
                   ^ "1. the first part of the instantiation " ^ term-to-string t ^ "\n"
                   ^ "2. the synthesized type variable: " ^ x)
        h (TpVar x) | just tp' = h tp'
        h tp = yes-error ("We do not have a matching case for the instantiation value and synthesized type"
                         ^ " for an instantation.\n"
                       ^ "1. the first part of the instantiation " ^ term-to-string t ^ "\n"
                       ^ "2. the synthesized type: " ^ type-to-string tp ^ "\n"
                       ^ "3. the instantiation value: " ^ type-to-string tp)



synth-term s (Δ , b , r) (Eapp e e') (App t t') = synth-term s (Δ , b , r) e t ≫synth h 
  where h : type → synth-t type
        h (TpParens tp) = h tp
        h (AbsTp1 Pi x tp1 tp2) = 
          check-term synth-funcs s (Δ , b , r) e' t' tp1 ≫checksynth
          no-error ("" , term-subst-type r (rename-pred s b) t' x tp2) 
        h (TpArrow tp1 tp2) = 
          check-term synth-funcs s (Δ , b , r) e' t' tp1 ≫checksynth 
          no-error ("" , tp2)
        h (TpVar x) with lookup-type-var s (renamectxt-rep r x )
        h (TpVar x) | nothing =
          yes-error ("An undeclared type variable was synthesized for the first part of an application.\n"
                   ^ "1. the first part of the application: " ^ term-to-string t ^ "\n"
                   ^ "2. the synthesized type variable: " ^ x)
        h (TpVar x) | just tp' = h tp'
        h tp = yes-error ("We synthesized a non-functional type for the first part of an application.\n"
                       ^ "1. the first part of the application: " ^ term-to-string t ^ "\n"
                       ^ "2. the synthesized type: " ^ type-to-string tp)

synth-term s (Δ , b , r) (Rbeta e t' e') t with convert-term (check-term synth-funcs) s (Δ , b , r) e' t'
synth-term s (Δ , b , r) (Rbeta e t' e') t | nothing , m = 
  yes-error (m ^ "\nIn a reverse-beta proof, we could not convert the given term with the given evidence.\n" 
                 ^ "1. the term: " ^ term-to-string t' ^ "\n" 
                 ^ "2. the evidence: " ^ evidence-to-string e')
synth-term s (Δ , b , r) (Rbeta e t' e') t | just t1 , m =
  if eq-term s (bctxt-contains b) r t t1 then
    synth-term (add-msg m s) (Δ , b , r) e t'
  else
    yes-error (m ^ "\nIn a reverse-beta proof, we were able to convert the given term, but the result is not equal to the term we are\n"
             ^ "trying to synthesize a type for.\n"
             ^ "1. the term we converted to: " ^ term-to-string t1 ^ "\n"
             ^ "2. " ^ synth-term-errstr t)               

synth-term s (Δ , b , r) (Proj e i) t = 
  synth-term s (Δ , b , r) e t ≫synth h i
  where h : index → type → synth-t type
        h i (TpParens tp) = h i tp
        h i (TpVar x) with lookup-type-var s (renamectxt-rep r x) 
        h i (TpVar x) | nothing =
          yes-error ("Type variable " ^ x
                   ^ " was synthesized for evidence e while synthesizing with a projection of e.\n")
        h i (TpVar x) | just tp' = h i tp'
        h One (AbsTp1 Iota x tp1 tp2) = no-error ("" , tp1)
        h Two (AbsTp1 Iota x tp1 tp2) = no-error ("" , (term-subst-type r (rename-pred s b) t x tp2))
        h i tp = yes-error ("We synthesized a type which is not a iota-type, when synthesizing with a projection\n"
                       ^ "as the evidence.\n"
                       ^ "1. the term for which we synthesized a type: " ^ term-to-string t ^ "\n"
                       ^ "2. the synthesized type: " ^ type-to-string tp)

synth-term s Γ (Ctora x) trm with lookup-type-var s x
synth-term s Γ (Ctora x) trm | nothing =
  yes-error ("Constructor evidence (ζ-expression) is being used in its one-argument form, but the argument (variable) is not defined.\n"
           ^ "1. the argument (which is supposed to be a defined evidence variable): " ^ x ^ "\n"
           ^ "2. " ^ synth-term-errstr trm)   
synth-term s (Δ , b , r) (Ctora x) trm | just tp = h tp
  where h : type → synth-t type
        h (TpParens tp) = h tp
        h (Nu X k Θ tp) with ctorset-find-term s (Δ , b , r) trm Θ
        h (Nu X k Θ tp) | nothing = 
          yes-error ("Constructor evidence (ζ-expression) is being used, but we cannot find the term in question in the "
                   ^ "constructor set.\n"
                   ^ "1. the type whose kinding has been established: " ^ type-to-string (Nu X k Θ tp) ^ "\n"
                   ^ "2. " ^ synth-term-errstr trm)
        h (Nu X k Θ tp) | just tp' = no-error ("" , tp')
        h (TpVar x) with lookup-type-var s (renamectxt-rep r x)
        h (TpVar x) | nothing = 
          yes-error ("Constructor evidence (ζ-expression) is being used, but the subevidence given does not show kinding of a nu-type.\n"
                   ^ "1. the type proved: " ^ x)
        h (TpVar x) | just tp' = h tp'
        h t = 
          yes-error ("Constructor evidence (ζ-expression) is being used, but the subevidence given does not show kinding of a nu-type.\n"
                   ^ "1. the type proved: " ^ type-to-string t)
        

synth-term s Γ e trm = yes-error ("We have no matching case for synthesizing a type for the given term from the given evidence.\n"
                                ^ "1. the evidence: " ^ evidence-to-string e ^ "\n"
                                ^ "2. " ^ synth-term-errstr trm)

try-synth-term s (Δ , b , r) e trm tp = 
  synth-term s (Δ , b , r) e trm ≫synthcheck λ tp' → 
  if eq-type s (bctxt-contains b) r tp tp' then no-error ""
  else yes-error ("While trying to check a term against a type a different type was synthesized.\n"
                ^ "1. the term we are checking: " ^ term-to-string trm ^ "\n"
                ^ "2. the type we synthesized for it: " ^ type-to-string tp' ^ "\n"
                ^ "3. the type we are checking against: " ^ type-to-string tp)
synth-funcs = mk-s synth-type try-synth-type synth-term try-synth-term 