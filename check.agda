module check where

open import lib

open import cedille-types
open import check-util
open import conversion
open import defeq
open import free
open import lift
open import rename
open import syntax-util
open import subst
open import tpstate

{-# NO_TERMINATION_CHECK #-}
check-term : s-t → tpstate → ctxt → evidence → term → type → check-t
check-type : s-t → tpstate → ctxt → evidence → type → kind → check-t  
check-tk : s-t → tpstate → ctxt → evidence → tk → check-t  
check-kind : s-t → tpstate → ctxt → evidence → kind → check-t  
check-ctorset-k : s-t → tpstate → ctxt → evidence → ctorset → check-t
check-ctorset : s-t → tpstate → ctxt → evidence → ctorset → check-t
check-defh : s-t → tpstate → ctxt → def → error-t tpstate

check-term S s Γ (Eparens e) trm tp = check-term S s Γ e trm tp
check-term S s Γ e (Parens trm) tp = check-term S s Γ e trm tp
check-term S s Γ e trm (TpParens tp) = check-term S s Γ e trm tp
check-term S s (Δ , b , r) (Eprint c e) trm tp =
  no-error (show-evctxt-if c (Δ , b , r) ^ term-to-string r trm ^ " ⇐ " ^ type-to-string r tp ^ "\n") ≫check
  check-term S s (Δ , b , r) e trm tp
check-term S s (Δ , b , r) EholeSilent trm tp = no-error ("●.\n")
check-term S s (Δ , b , r) (Ehole c) trm tp = 
  no-error (show-evctxt-if c (Δ , b , r) ^ term-to-string r trm ^ " ⇐ " ^ type-to-string r tp ^ "\n")
check-term S s (Δ , b , r) (EholeNamed c n) trm tp =
  no-error (show-evctxt-if c (Δ , b , r) ^ n ^ " ∷ " ^ term-to-string r trm ^ " ⇐ " ^ type-to-string r tp ^ "\n")
check-term S s Γ (Elet d e') trm tp = check-defh S s Γ d ≫=err λ s' → check-term S s' Γ e' trm tp
check-term S s (Δ , b , r) (Xi u EclassNone e) (Lam x t) (TpArrow tp1 tp2) =
  -- rename x to x' if x is already declared
  let x' = rename-away s b r x in 
    check-term S s (evctxt-insert-typing Δ u (Var x') tp1 , bctxt-add b x' , r) e (App (Lam x t) (Var x')) tp2
check-term S s (Δ , b , r) (Xi u EclassNone e) (Lam x t) (AbsTp1 Pi y tp1 tp2) = 
  let x' = rename-away s b r x in 
    -- we rename y to x' as we continue checking t against tp2
    check-term S s (evctxt-insert-typing Δ u (Var x') tp1 , bctxt-add b x' , renamectxt-insert (renamectxt-insert r y x') x x')
      e (App (Lam x t) (Var x')) tp2
check-term S s (Δ , b , r) Checkmark (Lam x t) U = 
  if list-all (rename-pred s b) (free-vars (Lam x t)) then no-error "" 
  else yes-error ("We are checking a lambda-abstraction against the type 𝓤, but that abstraction has undeclared free variables.\n"
                ^ "1. the lambda-abstraction: " ^ term-to-string r (Lam x t) ^ "\n"
                ^ "2. the current context: " ^ evctxt-to-string r Δ)
check-term S s (Δ , b , r) (Eapp Beta e) (App (Lam x t) t') tp = check-term S s (Δ , b , r) e (term-subst-term r (rename-pred s b) t' x t) tp
check-term S s (Δ , b , r) (Pair e1 e2) t (AbsTp1 Iota x tp1 tp2) =
  check-term S s (Δ , b , r) e1 t tp1 ≫check check-term S s (Δ , b , r) e2 t (term-subst-type r (rename-pred s b) t x tp2)
check-term S s (Δ , b , r) e t (AbsTp1 Iota x tp1 tp2) = evwrong-term r t (AbsTp1 Iota x tp1 tp2)
check-term S s (Δ , b , r) (Xi u EclassNone e) t (AbsTp2 All x a tp) = 
  -- we need to rename x away from the free variables of t (and any other free or global variables)
  let fvs = free-vars t in
  let x' = rename-away-from x (λ x → rename-pred s b x || list-any (_=string_ x) fvs) r in
   check-term S s (evctxt-insert-tk Δ u x' a , bctxt-add b x' , renamectxt-insert r x x') e t tp

check-term S s Γ (Cast e checkCast e') t tp with convert-type (check-term S) s Γ e' tp 
check-term S s (Δ , b , r) (Cast e checkCast e') t tp | nothing , m = 
 yes-error (m ^ (newline-sep-if m "a") ^ "We could not convert the given type with the given evidence, while checking a cast-term.\n"
          ^ "1. the type: " ^ type-to-string r tp ^ "\n"
          ^ "2. the evidence: " ^ evidence-to-string r e' ^ "\n"
          ^ "3. " ^ synth-term-errstr r t)
check-term S s Γ (Cast e checkCast e') t tp | just tp' , m = no-error m ≫check check-term S s Γ e t tp'

{- only untyped defined variables need to be handled here, as bound and/or typed ones will be handled in synth-term.
   Here we are basically just unfolding untyped definitions. -}
check-term S s (Δ , b , r) e (Var x) tp with lookup-untyped-var s (renamectxt-rep r x)
check-term (mk-s _ _ _ try-synth-term) s (Δ , b , r) e (Var x) tp | nothing = try-synth-term s (Δ , b , r) e (Var x) tp
check-term S s (Δ , b , r) e (Var x) tp | just trm = check-term S s (Δ , b , r) e trm tp

check-term S s (Δ , b , r) e t (TpVar x) with lookup-type-var s (renamectxt-rep r x)
check-term S s (Δ , b , r) e t (TpVar x) | just tp = check-term S s (Δ , b , r) e t tp
check-term (mk-s _ _ _ try-synth-term) s (Δ , b , r) e t (TpVar x) | nothing = try-synth-term s (Δ , b , r) e t (TpVar x)

check-term (mk-s _ _ _ try-synth-term) s Γ (Evar u) trm tp = try-synth-term s Γ (Evar u) trm tp
check-term (mk-s _ _ _ try-synth-term) s Γ (Eapp u u') trm tp = try-synth-term s Γ (Eapp u u') trm tp
check-term (mk-s _ _ _ try-synth-term) s Γ (Rbeta e e' t') trm tp = try-synth-term s Γ (Rbeta e e' t') trm tp
check-term (mk-s _ _ _ try-synth-term) s Γ e (App t1 t2) tp = try-synth-term s Γ e (App t1 t2) tp
check-term (mk-s _ _ _ try-synth-term) s Γ (Ctora x) trm tp = try-synth-term s Γ (Ctora x) trm tp

check-term S s (Δ , b , r) e t tp = 
  yes-error ("We do not have a matching case for checking a term with the given evidence and type.\n"
            ^ "1. the term: " ^ term-to-string r t ^ "\n"
            ^ "2. the type: " ^ type-to-string r tp ^ "\n"
            ^ "3. the evidence: " ^ evidence-to-string r e)


check-type S s Γ (Eparens e) t k = check-type S s Γ e t k
check-type S s Γ e (TpParens t) k = check-type S s Γ e t k
check-type S s Γ e t (KndParens k) = check-type S s Γ e t k
check-type S s (Δ , b , r) (Eprint c e) t k =
  no-error (show-evctxt-if c (Δ , b , r) ^ type-to-string r t ^ " ⇐ " ^ kind-to-string r k ^ "\n") ≫check
  check-type S s (Δ , b , r) e t k
check-type S s (Δ , b , r) EholeSilent t k = no-error ("●.\n")
check-type S s (Δ , b , r) (Ehole c) t k =
  no-error (show-evctxt-if c (Δ , b , r) ^ type-to-string r t ^ " ⇐ " ^ kind-to-string r k ^ "\n")
check-type S s (Δ , b , r) (EholeNamed c n) t k =
  no-error (show-evctxt-if c (Δ , b , r) ^ n ^ " ∷ " ^ type-to-string r t ^ " ⇐ " ^ kind-to-string r k ^ "\n")
check-type S s Γ (Elet d e') t k = check-defh S s Γ d ≫=err λ s' → check-type S s' Γ e' t k
check-type S s Γ e t (KndVar x) with lookup-kind-var s x
check-type S s (Δ , b , r) e t (KndVar x) | nothing = 
  yes-error ("We encountered an undefined kind variable while checking a type.\n"
           ^ "1. the type we are checking: " ^ type-to-string r t ^ "\n"
           ^ "2. the undefined kind variable we are checking it against: " ^ x)
check-type S s Γ e t (KndVar x) | just k = check-type S s Γ e t k

-- nu types
check-type S s (Δ , b , r) e (Nu X k Θ T) k' with eq-kind s (bctxt-contains b) r k k'
check-type S s (Δ , b , r) e (Nu X k Θ T) k' | ff = 
  yes-error ("The kind of a nu-abstraction does not match the expected one.\n"
           ^ "1. The kind of the nu-abstraction: " ^ kind-to-string r k ^ "\n"
           ^ "2. The expected kind " ^ kind-to-string r k')
check-type S s (Δ , b , r) e (Nu X k Θ T) k' | tt with occurs-only-polarity X tt T 
check-type S s (Δ , b , r) e (Nu X k Θ T) k' | tt | ff =
  yes-error ("The variable bound by a nu-abstraction does not occur only positively in the body of the nu-abstraction.\n"
           ^ "1. The nu-abstraction: " ^ type-to-string r (Nu X k Θ T))
check-type S s (Δ , b , r) e (Nu X k Θ T) k' | tt | tt with check-ctors X Θ
check-type S s (Δ , b , r) e (Nu X k Θ T) k' | tt | tt | just m =
  yes-error ("The constructor set for a nu-abstraction does not satisfy the required constraints.\n"
           ^ "1. The nu-abstraction: " ^ type-to-string r (Nu X k Θ T) ^ "\n"
           ^ "2. The constraint violation: " ^ m)
check-type S s (Δ , b , r) (Enu u u' e e' e'' e''') (Nu X k Θ T) k' | tt | tt | nothing = 
  let X' = rename-away s b r X in
  let Δ' = evctxt-insert-kinding Δ u (TpVar X') k in
  let b' = bctxt-add b X' in
  let r' = renamectxt-insert r X X' in
    check-ctorset-k S s (Δ' , b' , r') e Θ ≫check 
    u-type s (bctxt-contains b) k ≫=err λ ta → 
    check-ctorset S s (Δ , b , r) e' (type-subst-ctorset r (rename-pred s b) ta X Θ) ≫check 
      let Δ'' = (evctxt-insert-ctorset Δ' u' Θ) in
       check-ctorset S s (Δ'' , b' , r') e'' (type-subst-ctorset r (rename-pred s b) T X Θ) ≫check 
       check-type S s (Δ'' , b' , r') e''' T k 
check-type S s (Δ , b , r) e (Nu X k Θ T) k' | tt | tt | nothing = evwrong-type r e (Nu X k Θ T) k'

-- the rule is the same for Iota and Pi
check-type S s (Δ , b , r) (Xi u (EclassSome e) e') (AbsTp1 _ x t1 t2) Star = 
  let x' = rename-away s b r x in
  check-type S s (Δ , b , r) e t1 Star ≫check 
    check-type S s (evctxt-insert-typing Δ u (Var x') t1 , bctxt-add b x' , renamectxt-insert r x x') e' t2 Star
check-type S s Γ Check (AbsTp1 o x t1 t2) Star = 
  check-type S s Γ (Xi x (EclassSome Check) Check) (AbsTp1 o x t1 t2) Star
check-type S s Γ (Earrow e e') (AbsTp1 Pi x t1 t2) Star = 
  check-type S s Γ e t1 Star ≫check check-type S s Γ e' t2 Star
check-type S s (Δ , b , r) e (AbsTp1 _ x t1 t2) Star = evwrong-type r e (AbsTp1 Pi x t1 t2) Star
check-type S s (Δ , b , r) e (AbsTp1 o x t1 t2) k = 
  yes-error ("A " ^ ip-to-string o ^ "-type is being checked against a kind which is not ★.\n"
           ^ "1. the " ^ ip-to-string o ^ "-type: " ^ type-to-string r (AbsTp1 Pi x t1 t2) ^ "\n"
           ^ "2. the kind " ^ kind-to-string r k)
check-type S s Γ Check (TpArrow t1 t2) Star = 
  check-type S s Γ Check t1 Star ≫check check-type S s Γ Check t2 Star
check-type S s Γ (Earrow e e') (TpArrow t1 t2) Star = 
  check-type S s Γ e t1 Star ≫check check-type S s Γ e' t2 Star
check-type S s (Δ , b , r) e (TpArrow t1 t2) Star = evwrong-type r e (TpArrow t1 t2) Star
check-type S s (Δ , b , r) e (TpArrow t1 t2) k = 
  yes-error ("An arrow type is being checked against a kind which is not ★.\n"
           ^ "1. the arrow type: " ^ type-to-string r (TpArrow t1 t2) ^ "\n"
           ^ "2. the kind " ^ kind-to-string r k)
check-type S s (Δ , b , r) (Xi u (EclassSome e) e') (AbsTp2 All x t1 t2) Star = 
  let x' = rename-away s b r x in
  check-tk S s (Δ , b , r) e t1 ≫check 
    check-type S s (evctxt-insert-tk Δ u x' t1 , bctxt-add b x' , renamectxt-insert r x x') e' t2 Star
check-type S s Γ Check (AbsTp2 All x t1 t2) Star = 
  check-type S s Γ (Xi x (EclassSome Check) Check) (AbsTp2 All x t1 t2) Star

check-type S s (Δ , b , r) Check (AbsTp2 Lambda x (Tkk k) t) k' = 
  check-type S s (Δ , b , r) (Xi x EclassNone Check) (AbsTp2 Lambda x (Tkk k) t) k' 
check-type S s (Δ , b , r) Check (AbsTp2 Lambda x (Tkt t1) t2) k = 
  check-type S s (Δ , b , r) (Xi x EclassNone Check) (AbsTp2 Lambda x (Tkt t1) t2) k 

check-type S s (Δ , b , r) (Xi u EclassNone e') (AbsTp2 Lambda x (Tkk k) t) (KndArrow k' k'') = 
  if eq-kind s (bctxt-contains b) r k k' then
    (let x' = rename-away s b r x in
       check-type S s (evctxt-insert-kinding Δ u (TpVar x') k , bctxt-add b x' , renamectxt-insert r x x') e' t k'')
  else
    yes-error ("The domain kind for a type-level lambda abstraction does not match the expected one.\n"
             ^ "1. the type-level lambda abstraction: " ^ type-to-string r (AbsTp2 Lambda x (Tkk k) t) ^ "\n"
             ^ "2. the expected kind: " ^ kind-to-string r (KndArrow k' k''))

check-type S s (Δ , b , r) (Xi u EclassNone e') (AbsTp2 Lambda x (Tkt t1) t2) (KndTpArrow t1' k) = 
  if eq-type s (bctxt-contains b) r t1 t1' then
    (let x' = rename-away s b r x in
       check-type S s (evctxt-insert-typing Δ u (Var x') t1 , bctxt-add b x' , renamectxt-insert r x x') e' t2 k)
  else
    yes-error ("The domain type for a type-level lambda abstraction does not match the expected one.\n"
             ^ "1. the type-level lambda abstraction: " ^ type-to-string r (AbsTp2 Lambda x (Tkt t1) t2) ^ "\n"
             ^ "2. the expected kind: " ^ kind-to-string r (KndTpArrow t1' k))

check-type S s (Δ , b , r) (Xi u EclassNone e') (AbsTp2 Lambda x (Tkk k) t) (KndPi y (Tkk k') k'') = 
  if eq-kind s (bctxt-contains b) r k k' then
    (let x' = rename-away s b r x in
       check-type S s (evctxt-insert-kinding Δ u (TpVar x') k , bctxt-add b x' , 
                     renamectxt-insert (renamectxt-insert r x x') y x') e' t k'')
  else
    yes-error ("The domain kind for a type-level lambda abstraction does not match the expected one.\n"
             ^ "1. the type-level lambda abstraction: " ^ type-to-string r (AbsTp2 Lambda x (Tkk k) t) ^ "\n"
             ^ "2. the expected kind: " ^ kind-to-string r (KndPi y (Tkk k') k''))

check-type S s (Δ , b , r) (Xi u EclassNone e') (AbsTp2 Lambda x (Tkt t1) t) (KndPi y (Tkt t1') k'') = 
  if eq-type s (bctxt-contains b) r t1 t1' then
    (let x' = rename-away s b r x in
       check-type S s (evctxt-insert-typing Δ u (Var x') t1 , bctxt-add b x' , 
                     renamectxt-insert (renamectxt-insert r x x') y x') e' t k'')
  else
    yes-error ("The domain kind for a type-level lambda abstraction does not match the expected one.\n"
             ^ "1. the type-level lambda abstraction: " ^ type-to-string r (AbsTp2 Lambda x (Tkt t1) t) ^ "\n"
             ^ "2. the expected kind: " ^ kind-to-string r (KndPi y (Tkt t1') k''))

check-type (mk-s _ try-synth-type _ _) s Γ e (TpVar x) k = try-synth-type s Γ e (TpVar x) k
check-type (mk-s _ try-synth-type _ _) s Γ e (TpApp t1 t2) k = try-synth-type s Γ e (TpApp t1 t2) k
check-type (mk-s _ try-synth-type _ _) s Γ e (TpAppt t1 t2) k = try-synth-type s Γ e (TpAppt t1 t2) k
check-type (mk-s _ try-synth-type _ _) s Γ e U k = try-synth-type s Γ e U k
check-type (mk-s _ try-synth-type _ _) s Γ e (Lft trm tp) k = try-synth-type s Γ e (Lft trm tp) k
check-type S s (Δ , b , r) a t k =
  yes-error ("We have no matching case for checking the given type against the given kind, with the given form"
           ^ " of evidence.\n"
           ^ "1. the type: " ^ type-to-string r t ^ "\n"
           ^ "2. the kind we are checking it against: " ^ kind-to-string r k) 

check-kind S s (Δ , b , r) (Eprint c e) k =
  no-error (show-evctxt-if c (Δ , b , r) ^ kind-to-string r k ^ " ⇐ □\n") ≫check
  check-kind S s (Δ , b , r) e k
check-kind S s (Δ , b , r) EholeSilent k = no-error ("●.\n")
check-kind S s (Δ , b , r) (Ehole c) k = no-error (show-evctxt-if c (Δ , b , r) ^ kind-to-string r k ^ " ⇐ □\n")
check-kind S s (Δ , b , r) (EholeNamed c n) k = no-error (show-evctxt-if c (Δ , b , r) ^ n ^ " ∷ " ^ kind-to-string r k ^ " ⇐ □\n")
check-kind S s Γ e (KndParens k) = check-kind S s Γ e k
check-kind S s Γ (Elet d e') k = check-defh S s Γ d ≫=err λ s' → check-kind S s' Γ e' k
check-kind S s Γ (Eparens e) k = check-kind S s Γ e k 
check-kind S s Γ e (KndVar v) with lookup-kind-var s v
check-kind S s Γ e (KndVar v) | nothing = 
  yes-error ("We encountered an undefined kind variable.\n1. the kind variable: " ^ v)
check-kind S s Γ e (KndVar v) | just k = check-kind S s Γ e k
check-kind S s Γ (Evar u) k with lookup-kind-var s u
check-kind S s (Δ , b , r) (Evar u) k | nothing =
  yes-error ("We encountered an undefined evidence variable while checking a kind.\n"
           ^ "1. the evidence variable: " ^ u ^ "\n"
           ^ "2. the kind: " ^ kind-to-string r k)
check-kind S s (Δ , b , r) (Evar u) k | just k' = 
  if eq-kind s (bctxt-contains b) r k k' then (no-error "")
  else (yes-error ("The defined evidence variable does not prove the required superkinding.\n"
                 ^ "1. the evidence variable: " ^ u ^ " ∷ " ^ kind-to-string r k' ^ " ⇐ □\n"
                 ^ "2. the kind to check: " ^ kind-to-string r k))

check-kind S s (Δ , b , r) Check (KndPi x a k) = 
  check-kind S s (Δ , b , r) (Xi x (EclassSome Check) Check) (KndPi x a k) 
check-kind S s (Δ , b , r) (Xi u (EclassSome e) e') (KndPi x a k) = 
  let x' = rename-away s b r x in
    check-tk S s (Δ , b , r) e a ≫check check-kind S s (evctxt-insert-tk Δ u x' a , bctxt-add b x' , renamectxt-insert r x x') e' k
check-kind S s Γ (Earrow l l') (KndPi x' a k) = check-tk S s Γ l a ≫check check-kind S s Γ l' k
check-kind S s (Δ , b , r) e (KndPi x' a k) = evwrong-kind r e (KndPi x' a k)
check-kind S s Γ (Xi _ (EclassSome e) e') (KndArrow k k') = check-kind S s Γ e k ≫check check-kind S s Γ e' k'
check-kind S s Γ (Earrow l l') (KndArrow k k') = check-kind S s Γ l k ≫check check-kind S s Γ l' k'
check-kind S s Γ Check (KndArrow k k') = check-kind S s Γ Check k ≫check check-kind S s Γ Check k'
check-kind S s (Δ , b , r) e (KndArrow k k') = evwrong-kind r e (KndArrow k k')
check-kind S s Γ (Xi u (EclassSome e) e') (KndTpArrow t k') = check-type S s Γ e t Star ≫check check-kind S s Γ e' k' 
check-kind S s Γ (Earrow l l') (KndTpArrow t k') = check-type S s Γ l t Star ≫check check-kind S s Γ l' k'
check-kind S s Γ Check (KndTpArrow t k') = check-type S s Γ Check t Star ≫check check-kind S s Γ Check k'
check-kind S s (Δ , b , r) e (KndTpArrow t k') = evwrong-kind r e (KndTpArrow t k')
check-kind S s Γ Check Star = no-error ""
check-kind S s (Δ , b , r) e Star = evwrong-kind r e Star

check-tk S s Γ e (Tkk k) = check-kind S s Γ e k
check-tk S s Γ e (Tkt t) = check-type S s Γ e t Star

check-ctorset-k S s (Δ , b , r) (Eprint c e) Θ =
 no-error (show-evctxt-if c (Δ , b , r) ^ ctorset-to-string r Θ ^ " ⇐ ★\n") ≫check check-ctorset-k S s (Δ , b , r) e Θ
check-ctorset-k S s (Δ , b , r) EholeSilent Θ = no-error ("●.\n")
check-ctorset-k S s (Δ , b , r) (Ehole c) Θ = no-error (show-evctxt-if c (Δ , b , r) ^ ctorset-to-string r Θ ^ " ⇐ ★\n")
check-ctorset-k S s (Δ , b , r) (EholeNamed c n) Θ = 
 no-error (show-evctxt-if c (Δ , b , r) ^ n ^ " ∷ " ^ ctorset-to-string r Θ ^ " ⇐ ★\n")
check-ctorset-k S s Γ (Eparens e) Θ = check-ctorset-k S s Γ e Θ
check-ctorset-k S s Γ (Elet d e') Θ = check-defh S s Γ d ≫=err λ s' → check-ctorset-k S s' Γ e' Θ

check-ctorset-k S s Γ (Pair e e') (Add trm tp Θ) = 
  check-type S s Γ e tp Star ≫check check-ctorset-k S s Γ e' Θ
check-ctorset-k S s (Δ , b , r) e (Add trm tp Θ) = evwrong-ctorset-k r (Add trm tp Θ)
check-ctorset-k S s Γ Check Empty = no-error ""
check-ctorset-k S s (Δ , b , r) l Empty = evwrong-ctorset-k r Empty

check-ctorset S s (Δ , b , r) (Eprint c e) Θ =
  no-error (show-evctxt-if c (Δ , b , r) ^ ctorset-to-string r Θ ^ "\n") ≫check check-ctorset S s (Δ , b , r) e Θ
check-ctorset S s (Δ , b , r) EholeSilent Θ = no-error "●.\n"
check-ctorset S s (Δ , b , r) (Ehole c) Θ = 
  no-error (show-evctxt-if c (Δ , b , r) ^ ctorset-to-string r Θ ^ "\n")
check-ctorset S s (Δ , b , r) (EholeNamed c n) Θ = no-error (show-evctxt-if c (Δ , b , r) ^ n ^ " ∷ " ^ ctorset-to-string r Θ ^ "\n")
check-ctorset S s Γ (Eparens e) Θ = check-ctorset S s Γ e Θ
check-ctorset S s Γ (Elet d e') Θ = check-defh S s Γ d ≫=err λ s' → check-ctorset S s' Γ e' Θ

check-ctorset S s Γ (Pair e1 e2) (Add trm tp Θ) = check-term S s Γ e1 trm tp ≫check check-ctorset S s Γ e2 Θ
check-ctorset S s (Δ , b , r) e (Add trm tp Θ) = evwrong-ctorset r (Add trm tp Θ)
check-ctorset S s Γ Check Empty = no-error ""
check-ctorset S s (Δ , b , r) e Empty = evwrong-ctorset r Empty

check-defh S s Γ (Tdefine v t) = 
  def-assert-free s Γ v ≫err no-error (add-untyped-term-def v t s)
check-defh S s (Δ , b , r) (Edefine v (Tp trm tp) e e') with rename-pred s b v 
check-defh S s (Δ , b , r) (Edefine v (Tp trm tp) e e') | ff =
  (check-type S s (Δ , b , r) e' tp Star ≫check check-term S s (Δ , b , r) e trm tp) ≫=err λ m →
  no-error (add-msg m (add-typed-term-def v trm tp s))
check-defh S s (Δ , b , r) (Edefine v (Tp trm tp) e e') | tt with untyped-equal-def s b r v trm
check-defh S s (Δ , b , r) (Edefine v (Tp trm tp) e e') | tt | nothing = yes-error (redefine-err v)
check-defh S s (Δ , b , r) (Edefine v (Tp trm tp) e e') | tt | just trm' =
  {- we allow adding a typed redefinition of a symbol, if its previous definition was an untyped
     definition with the same term.  We remove the untyped definition to avoid confusion later -}
  (check-type S s (Δ , b , r) e' tp Star ≫check check-term S s (Δ , b , r) e trm tp) ≫=err λ m → 
  no-error (add-msg m (redefine-untyped-var-as-typed s v trm' tp))
check-defh S s Γ (Edefine v (Knd tp knd) e e') =
  def-assert-free s Γ v ≫err (check-kind S s Γ e' knd ≫check check-type S s Γ e tp knd) ≫=err λ m → 
  no-error (add-msg m (add-kinded-type-def v tp knd s))
check-defh S s Γ (Kdefine v knd e) =
  def-assert-free s Γ v ≫err check-kind S s Γ e knd ≫=err λ m → no-error (add-msg m (add-kind-def v knd s))

check-def : s-t → tpstate → def → error-t tpstate
check-def S s d with check-defh S s (empty-evctxt , empty-bctxt , empty-renamectxt) d
check-def S s d | yes-error e = add-to-def-error (get-defined-symbol d) e 
check-def S s d | no-error x = no-error x

