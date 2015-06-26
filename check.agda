module check where

open import lib

open import cedille-types
open import conversion
open import defeq
open import rename
open import syntax-util
open import subst
open import tpstate

{-# NO_TERMINATION_CHECK #-}
u-type : tpstate → (var → 𝔹) → kind → error-t type
u-type s b (KndArrow k k') = u-type s b k' ≫=err λ r → no-error (AbsTp2 Lambda (tpstate-fresh-var s b "X" empty-renamectxt) (Tkk k) r)
u-type s b (KndParens k) = u-type s b k
u-type s b (KndPi x a k) =  u-type s b k ≫=err λ r → no-error (AbsTp2 Lambda x a r)
u-type s b (KndTpArrow t k) = u-type s b k ≫=err λ r → no-error (AbsTp2 Lambda (tpstate-fresh-var s b "x" empty-renamectxt) (Tkt t) r)
u-type s b (KndVar x) with lookup-kind-var s x
u-type s b (KndVar x) | nothing = yes-error ("No definition was found for kind variable " ^ x ^ " (should not happen.)")
u-type s b (KndVar x) | just k = u-type s b k
u-type s b Star = no-error U


{- the return type for all the check functions.  The returned string is
   information for the user about holes. -}
check-t : Set
check-t = error-t string

infixr 1 _≫check_ _≫synth_ _≫checksynth_ _≫synthcheck_

synth-t : Set → Set
synth-t A = error-t (string × A)

_≫check_ : check-t → check-t → check-t
no-error x ≫check no-error x' = no-error (x ^ x')
no-error x ≫check yes-error x' = yes-error (x ^ x')
yes-error x ≫check no-error x' = yes-error (x ^ (newline-sep-if x x') ^ x')
yes-error x ≫check yes-error x' = yes-error (x ^ (newline-sep-if x x') ^ x')

_≫synth_ : {A B : Set} → synth-t A → (A → synth-t B) → synth-t B
no-error (m , a) ≫synth f with f a 
no-error (m , a) ≫synth f | no-error (m' , b) = no-error (m ^ m' , b)
no-error (m , a) ≫synth f | yes-error m' = yes-error (m ^ m')
yes-error x ≫synth f = yes-error x

_≫checksynth_ : check-t → {A : Set} → synth-t A → synth-t A
no-error x ≫checksynth no-error (x' , r) = no-error (x ^ x' , r)
no-error x ≫checksynth yes-error x' = yes-error (x ^ x')
yes-error x ≫checksynth no-error (x' , r) = yes-error (x ^ (newline-sep-if x x') ^ x')
yes-error x ≫checksynth yes-error x' = yes-error (x ^ (newline-sep-if x x') ^ x')

_≫synthcheck_ : {A : Set} → synth-t A → (A → check-t) → check-t
no-error (m , a) ≫synthcheck f with f a 
no-error (m , a) ≫synthcheck f | no-error m' = no-error (m ^ m')
no-error (m , a) ≫synthcheck f | yes-error m' = yes-error (m ^ m')
yes-error x ≫synthcheck f = yes-error x

unimplemented : string → ∀{A : Set} → error-t A
unimplemented s = yes-error (s ^ " is currently unimplemented.\n")

evwrong-kind : evidence → kind → check-t
evwrong-kind e k = 
  yes-error ("The wrong form of evidence was given for checking a kind.\n" 
              ^ "1. the evidence: " ^ evidence-to-string e ^ "\n"
              ^ "2. the kind: " ^ kind-to-string k)

evwrong-type : evidence → type → kind → check-t
evwrong-type e t k = 
  yes-error ("The wrong form of evidence was given for checking a kinding.\n"
           ^ "1. the evidence: " ^ evidence-to-string e ^ "\n"
           ^ "2. the kinding: " ^ type-to-string t ^ " : " ^ kind-to-string k)

evwrong-ctorset-k : ctorset → check-t
evwrong-ctorset-k Θ = 
  yes-error ("Encountered the wrong form of evidence for checking that the following ctor set is kindable:\n"
           ^ ctorset-to-string Θ)

evwrong-ctorset : ctorset → check-t
evwrong-ctorset Θ = 
  yes-error ("Encountered the wrong form of evidence for checking the following ctor set:\n"
           ^ ctorset-to-string Θ)

evwrong-term : term → type → check-t
evwrong-term x y = 
  yes-error ("Encountered the wrong form of evidence for checking the following typing:\n"
           ^ term-to-string x ^ " : " ^ type-to-string y)

holewrong-type : type → synth-t kind
holewrong-type l = 
  yes-error ("A hole is being used where we need to synthesize a kind for the following type:\n"
           ^ type-to-string l)

holewrong-term : term → synth-t type
holewrong-term t = 
  yes-error ("A hole is being used where we need to synthesize a type for the following term:\n"
           ^ term-to-string t)

synth-type-errstr : type → string
synth-type-errstr t = "the type whose kind we are trying to synthesize: " ^ type-to-string t

synth-term-errstr : term → string
synth-term-errstr t = "the term whose type we are trying to synthesize: " ^ term-to-string t

add-to-def-error : string → string → error-t tpstate
add-to-def-error v m = yes-error ("While checking the definition of " ^ v ^ ":\n" ^ m)

redefine-err : var → string
redefine-err x = "The symbol " ^ x ^ " is being redefined (not allowed).\n"
def-assert-free : tpstate → ctxt → var → error-t ⊤
def-assert-free s (Δ , b , r) x =
 if rename-pred s b x then yes-error (redefine-err x) else no-error triv

ctorset-find-term : tpstate → ctxt → term → ctorset → maybe type
ctorset-find-term s (Δ , b , r) t (Add trm tp Θ₁) with eq-term s (bctxt-contains b) r t trm
ctorset-find-term s (Δ , b , r) t (Add trm tp Θ₁) | tt = just tp
ctorset-find-term s (Δ , b , r) t (Add trm tp Θ₁) | ff = ctorset-find-term s (Δ , b , r) t Θ₁
ctorset-find-term s (Δ , b , r) t Empty = nothing

{-# NO_TERMINATION_CHECK #-}
check-term : tpstate → ctxt → evidence → term → type → check-t
check-type : tpstate → ctxt → evidence → type → kind → check-t  
check-tk : tpstate → ctxt → evidence → tk → check-t  
check-kind : tpstate → ctxt → evidence → kind → check-t  
check-ctorset-k : tpstate → ctxt → evidence → ctorset → check-t
check-ctorset : tpstate → ctxt → evidence → ctorset → check-t
check-defh : tpstate → ctxt → def → error-t tpstate

synth-type : tpstate → ctxt → evidence → type → synth-t kind
try-synth-type : tpstate → ctxt → evidence → type → kind → check-t

synth-term : tpstate → ctxt → evidence → term → synth-t type
try-synth-term : tpstate → ctxt → evidence → term → type → check-t

synth-type s Γ (Eparens e) t = synth-type s Γ e t
synth-type s Γ e (TpParens t) = synth-type s Γ e t
synth-type s Γ (Eprint c e) t = 
  synth-type s Γ e t ≫synth λ k → 
  no-error ((show-evctxt-if c Γ ^ type-to-string t ^ " ⇒ " ^ kind-to-string k ^ "\n") , k)
synth-type s Γ (Ehole _) t = holewrong-type t
synth-type s Γ (EholeNamed _ _) t = holewrong-type t
synth-type s Γ (Elet d e') t = check-defh s Γ d ≫=err λ s' → synth-type s' Γ e' t

synth-type s (Δ , b , r) (Evar u) t with evctxt-lookup Δ u 
synth-type s (Δ , b , r) (Evar u) t | nothing with lookup-type-var-k s u 
synth-type s (Δ , b , r) (Evar u) t | nothing | nothing =
  yes-error ("An evidence variable was found to be undeclared while attempting to synthesize a kind.\n"
           ^ "1. the evidence variable: " ^ u ^ "\n"
           ^ "2. " ^ synth-type-errstr t)
synth-type s (Δ , b , r) (Evar u) t | nothing | just k = no-error ("" , k)
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
          check-type s (Δ , b , r) e' t' k1 ≫checksynth no-error ("" , k2) 
        h (KndPi x (Tkk k1) k2) = 
          check-type s (Δ , b , r) e' t' k1 ≫checksynth no-error ("" , type-subst-kind r (rename-pred s b) t' x k2) 

        h (KndVar x) with lookup-kind-var s (renamectxt-rep r x )
        h (KndVar x) | nothing =
          yes-error ("An undeclared kind variable was synthesized for the first part of a type-level application.\n"
                   ^ "1. the first part of the application: " ^ type-to-string t ^ "\n"
                   ^ "2. the synthesized kind variable: " ^ x)
        h (KndVar x) | just k' = h k'
        h k = yes-error ("We synthesized a non-functional kind for the first part of a type-level application.\n"
                       ^ "1. the first part of the application: " ^ type-to-string t ^ "\n"
                       ^ "2. the synthesized kind: " ^ kind-to-string k)

synth-type s (Δ , b , r) (Eapp e e') (TpAppt t t') = synth-type s (Δ , b , r) e t ≫synth h 
  where h : kind → synth-t kind
        h (KndParens k) = h k
        h (KndTpArrow tp k) = 
          check-term s (Δ , b , r) e' t' tp ≫checksynth no-error ("" , k) 
        h (KndPi x (Tkt tp) k) = 
          check-term s (Δ , b , r) e' t' tp ≫checksynth no-error ("" , term-subst-kind r (rename-pred s b) t' x k) 

        h (KndVar x) with lookup-kind-var s (renamectxt-rep r x )
        h (KndVar x) | nothing =
          yes-error ("An undeclared kind variable was synthesized for the first part of a type-level application.\n"
                   ^ "1. the first part of the application: " ^ type-to-string t ^ "\n"
                   ^ "2. the synthesized kind variable: " ^ x)
        h (KndVar x) | just k' = h k'
        h k = yes-error ("We synthesized a non-functional kind for the first part of a type-level application.\n"
                       ^ "1. the first part of the application: " ^ type-to-string t ^ "\n"
                       ^ "2. the synthesized kind: " ^ kind-to-string k)

synth-type s (Δ , b , r) (Xi u EclassNone e) (Lft x trm ltp) =
  let x' = rename-away s b r x in
    check-term s (evctxt-insert-kinding Δ u (TpVar x) Star , bctxt-add b x' , renamectxt-insert r x x')
       e trm (lift-liftingType ltp) ≫checksynth
    no-error ("" , lift-to-kind ltp)

synth-type s Γ e t = 
  yes-error ("We have no matching case for synthesizing a kind for the given type, with the given evidence.\n"
            ^ "1. the type " ^ type-to-string t)


try-synth-type s (Δ , b , r) e t k = 
  synth-type s (Δ , b , r) e t ≫synthcheck λ k' → 
  if eq-kind s (bctxt-contains b) r k k' then no-error "" 
  else (yes-error ("While trying to check a type against a kind, a different kind was synthesized.\n"
                ^ "1. the type we are checking: " ^ type-to-string t ^ "\n"
                ^ "2. the kind we synthesized for it: " ^ kind-to-string k' ^ "\n"
                ^ "3. the kind we are checking against: " ^ kind-to-string k))
  
synth-term s Γ (Eparens e) trm = synth-term s Γ e trm
synth-term s Γ (Eprint c e) trm = 
  synth-term s Γ e trm ≫synth λ tp →
  no-error ((show-evctxt-if c Γ ^ term-to-string trm ^ " ⇒ " ^ type-to-string tp ^ "\n") , tp)
synth-term s Γ (Ehole _) trm = holewrong-term trm
synth-term s Γ (EholeNamed _ _) trm = holewrong-term trm
synth-term s Γ (Elet d e) trm = check-defh s Γ d ≫=err λ s' → synth-term s' Γ e trm

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
        h tp with synth-conversion-type s Γ e' tp 
        h tp | just tp' , m = no-error (m , tp')
        h tp | nothing , m = yes-error m 

synth-term s (Δ , b , r) (Eapp e (Eappt e' t')) t =
  synth-term s (Δ , b , r) e t ≫synth h 
  where h : type → synth-t type
        h (TpParens tp) = h tp 
        h (AbsTp2 All x (Tkt tp) tp2) = 
          check-term s (Δ , b , r) e' t' tp ≫checksynth no-error ("" , term-subst-type r (rename-pred s b) t' x tp2) 
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
          check-type s (Δ , b , r) e' tp k ≫checksynth no-error ("" , type-subst-type r (rename-pred s b) tp x tp2) 
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
          check-term s (Δ , b , r) e' t' tp1 ≫checksynth no-error ("" , term-subst-type r (rename-pred s b) t' x tp2) 
        h (TpArrow tp1 tp2) = 
          check-term s (Δ , b , r) e' t' tp1 ≫checksynth no-error ("" , tp2)
        h (TpVar x) with lookup-type-var s (renamectxt-rep r x )
        h (TpVar x) | nothing =
          yes-error ("An undeclared type variable was synthesized for the first part of an application.\n"
                   ^ "1. the first part of the application: " ^ term-to-string t ^ "\n"
                   ^ "2. the synthesized type variable: " ^ x)
        h (TpVar x) | just tp' = h tp'
        h tp = yes-error ("We synthesized a non-functional type for the first part of an application.\n"
                       ^ "1. the first part of the application: " ^ term-to-string t ^ "\n"
                       ^ "2. the synthesized type: " ^ type-to-string tp)

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
        

synth-term s Γ e trm = yes-error "Unimplemented part of synth-term"

try-synth-term s (Δ , b , r) e trm tp = 
  synth-term s (Δ , b , r) e trm ≫synthcheck λ tp' → 
  if eq-type s (bctxt-contains b) r tp tp' then no-error ""
  else yes-error ("While trying to check a term against a type a different type was synthesized.\n"
                ^ "1. the term we are checking: " ^ term-to-string trm ^ "\n"
                ^ "2. the type we synthesized for it: " ^ type-to-string tp' ^ "\n"
                ^ "3. the type we are checking against: " ^ type-to-string tp)

check-term s Γ (Eparens e) trm tp = check-term s Γ e trm tp
check-term s Γ e (Parens trm) tp = check-term s Γ e trm tp
check-term s Γ e trm (TpParens tp) = check-term s Γ e trm tp
check-term s Γ (Eprint c e) trm tp =
  no-error (show-evctxt-if c Γ ^ term-to-string trm ^ " ⇐ " ^ type-to-string tp ^ "\n") ≫check
  check-term s Γ e trm tp
check-term s Γ (Ehole c) trm tp = no-error (show-evctxt-if c Γ ^ term-to-string trm ^ " ⇐ " ^ type-to-string tp ^ "\n")
check-term s Γ (EholeNamed c n) trm tp = no-error (show-evctxt-if c Γ ^ n ^ " ∷ " ^ term-to-string trm ^ " ⇐ " ^ type-to-string tp ^ "\n")
check-term s Γ (Elet d e') trm tp = check-defh s Γ d ≫=err λ s' → check-term s' Γ e' trm tp
check-term s (Δ , b , r) (Xi u EclassNone e) (Lam x t) (TpArrow tp1 tp2) =
  -- rename x to x' if x is already declared
  let x' = rename-away s b r x in 
    check-term s (evctxt-insert-typing Δ u (Var x') tp1 , bctxt-add b x' , r) e (App (Lam x t) (Var x')) tp2
check-term s (Δ , b , r) (Xi u EclassNone e) (Lam x t) (AbsTp1 Pi y tp1 tp2) = 
  let x' = rename-away s b r x in 
    -- we rename y to x' as we continue checking t against tp2
    check-term s (evctxt-insert-typing Δ u (Var x') tp1 , bctxt-add b x' , renamectxt-insert (renamectxt-insert r y x') x x')
      e (App (Lam x t) (Var x')) tp2
check-term s (Δ , b , r) Checkmark (Lam x t) U = 
  if list-all (rename-pred s b) (free-vars (Lam x t)) then no-error "" 
  else yes-error ("We are checking a lambda-abstraction against the type 𝓤, but that abstraction has undeclared free variables.\n"
                ^ "1. the lambda-abstraction: " ^ term-to-string (Lam x t) ^ "\n"
                ^ "2. the current context: " ^ evctxt-to-string Δ)
check-term s (Δ , b , r) (Eapp Beta e) (App (Lam x t) t') tp = check-term s (Δ , b , r) e (term-subst-term r (rename-pred s b) t' x t) tp
check-term s (Δ , b , r) (Pair e1 e2) t (AbsTp1 Iota x tp1 tp2) =
  check-term s (Δ , b , r) e1 t tp1 ≫check check-term s (Δ , b , r) e2 t (term-subst-type r (rename-pred s b) t x tp2)
check-term s Γ e t (AbsTp1 Iota x tp1 tp2) = evwrong-term t (AbsTp1 Iota x tp1 tp2)
check-term s (Δ , b , r) (Xi u EclassNone e) t (AbsTp2 All x a tp) = 
  -- we need to rename x away from the free variables of t (and any other free or global variables)
  let fvs = free-vars t in
  let x' = rename-away-from x (λ x → rename-pred s b x || list-any (_=string_ x) fvs) r in
   check-term s (evctxt-insert-tk Δ u x' a , bctxt-add b x' , renamectxt-insert r x x') e t tp

{- only untyped defined variables need to be handled here, as bound and/or typed ones will be handled in synth-term.
   Here we are basically just unfolding untyped definitions. -}
check-term s (Δ , b , r) e (Var x) tp with lookup-untyped-var s (renamectxt-rep r x)
check-term s (Δ , b , r) e (Var x) tp | nothing = try-synth-term s (Δ , b , r) e (Var x) tp
check-term s (Δ , b , r) e (Var x) tp | just trm = check-term s (Δ , b , r) e trm tp
check-term s Γ (Cast e checkCast e') t tp with synth-conversion-type s Γ e' tp 
check-term s Γ (Cast e checkCast e') t tp | nothing , m = 
 yes-error (m ^ (newline-sep-if m "a") ^ "We could not convert the given type with the given evidence, while checking a cast-term.\n"
          ^ "1. the type: " ^ type-to-string tp ^ "\n"
          ^ "2. the evidence: " ^ evidence-to-string e' ^ "\n"
          ^ "3. " ^ synth-term-errstr t)
check-term s Γ (Cast e checkCast e') t tp | just tp' , m = no-error m ≫check check-term s Γ e t tp'

check-term s Γ (Evar u) trm tp = try-synth-term s Γ (Evar u) trm tp
check-term s Γ e (App t1 t2) tp = try-synth-term s Γ e (App t1 t2) tp
check-term s Γ (Ctora x) trm tp = try-synth-term s Γ (Ctora x) trm tp

check-term s Γ e t (TpVar x) with lookup-type-var s x
check-term s Γ e t (TpVar x) | just tp = check-term s Γ e t tp
check-term s Γ e t (TpVar x) | nothing = 
  yes-error ("We have no matching case for checking the given term against the given type variable, with the given evidence.\n"
            ^ "1. the term: " ^ term-to-string t ^ "\n"
            ^ "2. the type variable: " ^ x)

check-term s Γ e t tp = 
  yes-error ("We do not have a matching case for checking a term with the given evidence and type.\n"
            ^ "1. the term: " ^ term-to-string t ^ "\n"
            ^ "2. the type: " ^ type-to-string tp)


check-type s Γ (Eparens e) t k = check-type s Γ e t k
check-type s Γ e (TpParens t) k = check-type s Γ e t k
check-type s Γ e t (KndParens k) = check-type s Γ e t k
check-type s Γ (Eprint c e) t k =
  no-error (show-evctxt-if c Γ ^ type-to-string t ^ " ⇐ " ^ kind-to-string k ^ "\n") ≫check
  check-type s Γ e t k
check-type s Γ (Ehole c) t k = no-error (show-evctxt-if c Γ ^ type-to-string t ^ " ⇐ " ^ kind-to-string k ^ "\n")
check-type s Γ (EholeNamed c n) t k = no-error (show-evctxt-if c Γ ^ n ^ " ∷ " ^ type-to-string t ^ " ⇐ " ^ kind-to-string k ^ "\n")
check-type s Γ (Elet d e') t k = check-defh s Γ d ≫=err λ s' → check-type s' Γ e' t k

-- nu types
check-type s (Δ , b , r) e (Nu X k Θ T) k' with eq-kind s (bctxt-contains b) r k k'
check-type s (Δ , b , r) e (Nu X k Θ T) k' | ff = 
  yes-error ("The kind of a nu-abstraction does not match the expected one.\n"
           ^ "1. The kind of the nu-abstraction: " ^ kind-to-string k ^ "\n"
           ^ "2. The expected kind " ^ kind-to-string k')
check-type s (Δ , b , r) e (Nu X k Θ T) k' | tt with occurs-only-polarity X tt T 
check-type s (Δ , b , r) e (Nu X k Θ T) k' | tt | ff =
  yes-error ("The variable bound by a nu-abstraction does not occur only positively in the body of the nu-abstraction.\n"
           ^ "1. The nu-abstraction: " ^ type-to-string (Nu X k Θ T))
check-type s (Δ , b , r) e (Nu X k Θ T) k' | tt | tt with check-ctors X Θ
check-type s (Δ , b , r) e (Nu X k Θ T) k' | tt | tt | just m =
  yes-error ("The constructor set for a nu-abstraction does not satisfy the required constraints.\n"
           ^ "1. The nu-abstraction: " ^ type-to-string (Nu X k Θ T) ^ "\n"
           ^ "2. The constraint violation: " ^ m)
check-type s (Δ , b , r) (Enu u u' e e' e'' e''') (Nu X k Θ T) k' | tt | tt | nothing = 
  let X' = rename-away s b r X in
  let Δ' = evctxt-insert-kinding Δ u (TpVar X') k in
  let b' = bctxt-add b X' in
  let r' = renamectxt-insert r X X' in
    check-ctorset-k s (Δ' , b' , r') e Θ ≫check 
    u-type s (bctxt-contains b) k ≫=err λ ta → 
    check-ctorset s (Δ , b , r) e' (type-subst-ctorset r (rename-pred s b) ta X Θ) ≫check 
      let Δ'' = (evctxt-insert-ctorset Δ' u' Θ) in
       check-ctorset s (Δ'' , b' , r') e'' (type-subst-ctorset r (rename-pred s b) T X Θ) ≫check 
       check-type s (Δ'' , b' , r') e''' T k 
check-type s (Δ , b , r) e (Nu X k Θ T) k' | tt | tt | nothing = evwrong-type e (Nu X k Θ T) k'

-- the rule is the same for Iota and Pi
check-type s (Δ , b , r) (Xi u (EclassSome e) e') (AbsTp1 _ x t1 t2) Star = 
  let x' = rename-away s b r x in
  check-type s (Δ , b , r) e t1 Star ≫check 
    check-type s (evctxt-insert-typing Δ u (Var x') t1 , bctxt-add b x' , renamectxt-insert r x x') e' t2 Star
check-type s Γ (Earrow e e') (AbsTp1 Pi x t1 t2) Star = 
  check-type s Γ e t1 Star ≫check check-type s Γ e' t2 Star
check-type s Γ e (AbsTp1 _ x t1 t2) Star = evwrong-type e (AbsTp1 Pi x t1 t2) Star
check-type s Γ e (AbsTp1 o x t1 t2) k = 
  yes-error ("A " ^ ip-to-string o ^ "-type is being checked against a kind which is not ★.\n"
           ^ "1. the " ^ ip-to-string o ^ "-type: " ^ type-to-string (AbsTp1 Pi x t1 t2) ^ "\n"
           ^ "2. the kind " ^ kind-to-string k)
check-type s Γ (Earrow e e') (TpArrow t1 t2) Star = 
  check-type s Γ e t1 Star ≫check check-type s Γ e' t2 Star
check-type s Γ e (TpArrow t1 t2) Star = evwrong-type e (TpArrow t1 t2) Star
check-type s Γ e (TpArrow t1 t2) k = 
  yes-error ("An arrow type is being checked against a kind which is not ★.\n"
           ^ "1. the arrow type: " ^ type-to-string (TpArrow t1 t2) ^ "\n"
           ^ "2. the kind " ^ kind-to-string k)
check-type s (Δ , b , r) (Xi u (EclassSome e) e') (AbsTp2 All x t1 t2) Star = 
  let x' = rename-away s b r x in
  check-tk s (Δ , b , r) e t1 ≫check 
    check-type s (evctxt-insert-tk Δ u x' t1 , bctxt-add b x' , renamectxt-insert r x x') e' t2 Star

check-type s (Δ , b , r) (Xi u EclassNone e') (AbsTp2 Lambda x (Tkk k) t) (KndArrow k' k'') = 
  if eq-kind s (bctxt-contains b) r k k' then
    (let x' = rename-away s b r x in
       check-type s (evctxt-insert-kinding Δ u (TpVar x') k , bctxt-add b x' , renamectxt-insert r x x') e' t k'')
  else
    yes-error ("The domain kind for a type-level lambda abstraction does not match the expected one.\n"
             ^ "1. the type-level lambda abstraction: " ^ type-to-string (AbsTp2 Lambda x (Tkk k) t) ^ "\n"
             ^ "2. the expected kind: " ^ kind-to-string (KndArrow k' k''))

check-type s (Δ , b , r) (Xi u EclassNone e') (AbsTp2 Lambda x (Tkt t1) t2) (KndTpArrow t1' k) = 
  if eq-type s (bctxt-contains b) r t1 t1' then
    (let x' = rename-away s b r x in
       check-type s (evctxt-insert-typing Δ u (Var x') t1 , bctxt-add b x' , renamectxt-insert r x x') e' t2 k)
  else
    yes-error ("The domain type for a type-level lambda abstraction does not match the expected one.\n"
             ^ "1. the type-level lambda abstraction: " ^ type-to-string (AbsTp2 Lambda x (Tkt t1) t2) ^ "\n"
             ^ "2. the expected kind: " ^ kind-to-string (KndTpArrow t1' k))

check-type s (Δ , b , r) (Xi u EclassNone e') (AbsTp2 Lambda x (Tkk k) t) (KndPi y (Tkk k') k'') = 
  if eq-kind s (bctxt-contains b) r k k' then
    (let x' = rename-away s b r x in
       check-type s (evctxt-insert-kinding Δ u (TpVar x') k , bctxt-add b x' , 
                     renamectxt-insert (renamectxt-insert r x x') y x') e' t k'')
  else
    yes-error ("The domain kind for a type-level lambda abstraction does not match the expected one.\n"
             ^ "1. the type-level lambda abstraction: " ^ type-to-string (AbsTp2 Lambda x (Tkk k) t) ^ "\n"
             ^ "2. the expected kind: " ^ kind-to-string (KndPi y (Tkk k') k''))

check-type s (Δ , b , r) (Xi u EclassNone e') (AbsTp2 Lambda x (Tkt t1) t) (KndPi y (Tkt t1') k'') = 
  if eq-type s (bctxt-contains b) r t1 t1' then
    (let x' = rename-away s b r x in
       check-type s (evctxt-insert-typing Δ u (Var x') t1 , bctxt-add b x' , 
                     renamectxt-insert (renamectxt-insert r x x') y x') e' t k'')
  else
    yes-error ("The domain kind for a type-level lambda abstraction does not match the expected one.\n"
             ^ "1. the type-level lambda abstraction: " ^ type-to-string (AbsTp2 Lambda x (Tkt t1) t) ^ "\n"
             ^ "2. the expected kind: " ^ kind-to-string (KndPi y (Tkt t1') k''))

check-type s Γ e (TpApp t1 t2) k = try-synth-type s Γ e (TpApp t1 t2) k
check-type s Γ e (TpAppt t1 t2) k = try-synth-type s Γ e (TpAppt t1 t2) k
check-type s Γ e (TpVar x) k = try-synth-type s Γ e (TpVar x) k
check-type s Γ e U k = try-synth-type s Γ e U k
check-type s Γ e (Lft x trm tp) k = try-synth-type s Γ e (Lft x trm tp) k
check-type s Γ a t k = yes-error ("We have no matching case for checking the given type against the given kind, with the given form"
                                ^ " of evidence.\n"
                                ^ "1. the type: " ^ type-to-string t ^ "\n"
                                ^ "2. the kind we are checking it against: " ^ kind-to-string k) 

check-kind s Γ (Eprint c e) k =
  no-error (show-evctxt-if c Γ ^ kind-to-string k ^ " ⇐ □\n") ≫check
  check-kind s Γ e k
check-kind s Γ (Ehole c) k = no-error (show-evctxt-if c Γ ^ kind-to-string k ^ " ⇐ □\n")
check-kind s Γ (EholeNamed c n) k = no-error (show-evctxt-if c Γ ^ n ^ " ∷ " ^ kind-to-string k ^ " ⇐ □\n")
check-kind s Γ e (KndParens k) = check-kind s Γ e k
check-kind s Γ (Elet d e') k = check-defh s Γ d ≫=err λ s' → check-kind s' Γ e' k
check-kind s Γ (Eparens e) k = check-kind s Γ e k 

check-kind s (Δ , b , r) (Xi u (EclassSome e) e') (KndPi x a k) = 
  let x' = rename-away s b r x in
    check-tk s (Δ , b , r) e a ≫check check-kind s (evctxt-insert-tk Δ u x' a , bctxt-add b x' , renamectxt-insert r x x') e' k
check-kind s Γ (Earrow l l') (KndPi x' a k) = check-tk s Γ l a ≫check check-kind s Γ l' k
check-kind s Γ e (KndPi x' a k) = evwrong-kind e (KndPi x' a k)
check-kind s Γ (Xi _ (EclassSome e) e') (KndArrow k k') = check-kind s Γ e k ≫check check-kind s Γ e' k'
check-kind s Γ (Earrow l l') (KndArrow k k') = check-kind s Γ l k ≫check check-kind s Γ l' k'
check-kind s Γ e (KndArrow k k') = evwrong-kind e (KndArrow k k')
check-kind s Γ (Xi u (EclassSome e) e') (KndTpArrow t k') = check-type s Γ e t Star ≫check check-kind s Γ e' k' 
check-kind s Γ (Earrow l l') (KndTpArrow t k') = check-type s Γ l t Star ≫check check-kind s Γ l' k'
check-kind s Γ e (KndTpArrow t k') = evwrong-kind e (KndTpArrow t k')
check-kind s Γ Check Star = no-error ""
check-kind s Γ e Star = evwrong-kind e Star
check-kind s Γ (Evar u) (KndVar v) with u =string v 
check-kind s Γ (Evar u) (KndVar v) | tt = no-error ""
check-kind s Γ (Evar u) (KndVar v) | ff = 
  yes-error ("The defined evidence symbol does not prove the required superkinding.\n"
           ^ "1. the evidence variable: " ^ u ^ "\n"
           ^ "2. the kind variable to check: " ^ v)
check-kind s Γ e (KndVar v) = evwrong-kind e (KndVar v)

check-tk s Γ e (Tkk k) = check-kind s Γ e k
check-tk s Γ e (Tkt t) = check-type s Γ e t Star

check-ctorset-k s Γ (Eprint c e) Θ = no-error (show-evctxt-if c Γ ^ ctorset-to-string Θ ^ " ⇐ ★\n") ≫check check-ctorset-k s Γ e Θ
check-ctorset-k s Γ (Ehole c) Θ = no-error (show-evctxt-if c Γ ^ ctorset-to-string Θ ^ " ⇐ ★\n")
check-ctorset-k s Γ (EholeNamed c n) Θ = no-error (show-evctxt-if c Γ ^ n ^ " ∷ " ^ ctorset-to-string Θ ^ " ⇐ ★\n")
check-ctorset-k s Γ (Eparens e) Θ = check-ctorset-k s Γ e Θ
check-ctorset-k s Γ (Elet d e') Θ = check-defh s Γ d ≫=err λ s' → check-ctorset-k s' Γ e' Θ

check-ctorset-k s Γ (Pair e e') (Add trm tp Θ) = 
  check-type s Γ e tp Star ≫check check-ctorset-k s Γ e' Θ
check-ctorset-k s Γ e (Add trm tp Θ) = evwrong-ctorset-k (Add trm tp Θ)
check-ctorset-k s Γ Check Empty = no-error ""
check-ctorset-k s Γ l Empty = evwrong-ctorset-k Empty

check-ctorset s Γ (Eprint c e) Θ = no-error (show-evctxt-if c Γ ^ ctorset-to-string Θ ^ "\n") ≫check check-ctorset s Γ e Θ
check-ctorset s Γ (Ehole c) Θ = no-error (show-evctxt-if c Γ ^ ctorset-to-string Θ ^ "\n")
check-ctorset s Γ (EholeNamed c n) Θ = no-error (show-evctxt-if c Γ ^ n ^ " ∷ " ^ ctorset-to-string Θ ^ "\n")
check-ctorset s Γ (Eparens e) Θ = check-ctorset s Γ e Θ
check-ctorset s Γ (Elet d e') Θ = check-defh s Γ d ≫=err λ s' → check-ctorset s' Γ e' Θ

check-ctorset s Γ (Pair e1 e2) (Add trm tp Θ) = check-term s Γ e1 trm tp ≫check check-ctorset s Γ e2 Θ
check-ctorset s Γ e (Add trm tp Θ) = evwrong-ctorset (Add trm tp Θ)
check-ctorset s Γ Check Empty = no-error ""
check-ctorset s Γ e Empty = evwrong-ctorset Empty

check-defh s Γ (Tdefine v t) = 
  def-assert-free s Γ v ≫err no-error (add-untyped-term-def v t s)
check-defh s (Δ , b , r) (Edefine v (Tp trm tp) e e') with rename-pred s b v 
check-defh s (Δ , b , r) (Edefine v (Tp trm tp) e e') | ff =
  (check-type s (Δ , b , r) e' tp Star ≫check check-term s (Δ , b , r) e trm tp) ≫=err λ m →
  no-error (add-msg m (add-typed-term-def v trm tp s))
check-defh s (Δ , b , r) (Edefine v (Tp trm tp) e e') | tt with lookup-untyped-var s v
check-defh s (Δ , b , r) (Edefine v (Tp trm tp) e e') | tt | nothing = yes-error (redefine-err v)
check-defh s (Δ , b , r) (Edefine v (Tp trm tp) e e') | tt | just trm' with eq-term s (bctxt-contains b) r trm trm'
check-defh s (Δ , b , r) (Edefine v (Tp trm tp) e e') | tt | just trm' | ff = yes-error (redefine-err v)
check-defh s (Δ , b , r) (Edefine v (Tp trm tp) e e') | tt | just trm' | tt = 
  {- we allow adding a typed redefinition of a symbol, if its previous definition was an untyped
     definition with the same term -}
  (check-type s (Δ , b , r) e' tp Star ≫check check-term s (Δ , b , r) e trm tp) ≫=err λ m → 
  no-error (add-msg m (add-typed-term-def v trm' tp s))
check-defh s Γ (Edefine v (Knd tp knd) e e') =
  def-assert-free s Γ v ≫err (check-kind s Γ e' knd ≫check check-type s Γ e tp knd) ≫=err λ m → 
  no-error (add-msg m (add-kinded-type-def v tp knd s))
check-defh s Γ (Kdefine v knd e) =
  def-assert-free s Γ v ≫err check-kind s Γ e knd ≫=err λ m → no-error (add-msg m (add-kind-def v knd s))

check-def : tpstate → def → error-t tpstate
check-def s d with check-defh s (empty-evctxt , empty-bctxt , empty-renamectxt) d
check-def s d | yes-error e = add-to-def-error (get-defined-symbol d) e 
check-def s d | no-error x = no-error x