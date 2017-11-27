{- Module that generates semi-blank spans for the beta-reduction buffer -}

open import lib
open import ctxt

module erased-spans where

open import cedille-types
open import spans
open import syntax-util
open import to-string


{- Helper functions -}

get-loc-h : var → ctxt → tagged-val

get-loc : var → spanM tagged-val
get-loc v = get-ctxt (λ Γ → spanMr (get-loc-h v Γ))

get-loc-h v Γ with ctxt-get-info v Γ
get-loc-h v Γ | just (_ , (fp , pos)) = ("location" , fp ^ " - " ^ pos)
get-loc-h v Γ | nothing = ("location" , "missing - missing")

defTermOrType-start-pos : defTermOrType → posinfo
defTermOrType-start-pos (DefTerm pi _ _ _) = pi
defTermOrType-start-pos (DefType pi _ _ _) = pi

symbol-tv : string → tagged-val
symbol-tv s = "symbol" , s

{- Span functions -}
erased-term-spans : term → spanM ⊤
erased-type-spans : type → spanM ⊤
erased-kind-spans : kind → spanM ⊤
error-spans : string → spanM ⊤
error-spans s = λ Γ → λ ss → triv , Γ , (global-error s nothing)

inc-pi : posinfo → posinfo
inc-pi pi = posinfo-plus pi 1

put-span : posinfo → posinfo → language-level → 𝕃 tagged-val → spanM ⊤
put-span pi pi' ll tv = spanM-add (mk-span "" (inc-pi pi) (inc-pi pi') (ll-data ll :: tv))

pi-plus-span : posinfo → string → language-level → 𝕃 tagged-val → spanM ⊤
pi-plus-span pi s = put-span pi (posinfo-plus-str pi s)

inc-span : posinfo → language-level → 𝕃 tagged-val → spanM ⊤
inc-span pi = put-span pi (inc-pi pi)

{-
nav-span : posinfo → spanM ⊤
nav-span pi = spanM-add (mk-span "" pi (inc-pi pi) (punctuation-data :: not-for-navigation :: []))

nav-span-big : posinfo → posinfo → spanM ⊤
nav-span-big pi pi' = spanM-add (mk-span "" pi pi' (punctuation-data :: not-for-navigation :: []))
-}

optTerm-span : optTerm → spanM ⊤
optTerm-span NoTerm = spanMok
optTerm-span (SomeTerm t pi) = erased-term-spans t

optType-span : optType → spanM ⊤
optType-span NoType = spanMok
optType-span (SomeType tp) = erased-type-spans tp

ll-type-data : language-level → tagged-val
ll-type-data ll-term = "type" , "br-auto-generated-type"
ll-type-data ll-type = "kind" , "br-auto-generated-kind"
ll-type-data ll-kind = "superkind" , "br-auto-generated-superkind"

erased-var-span : posinfo → var → language-level → spanM ⊤
erased-var-span _ "_" _ = spanMok
erased-var-span pi v ll = get-loc v ≫=span λ loc →
  pi-plus-span pi v ll (ll-type-data ll :: symbol-tv v :: loc :: [])

defTermOrType-span : defTermOrType → spanM ⊤
defTermOrType-span (DefTerm pi x m t) = erased-var-span pi x ll-term ≫span erased-term-spans t
defTermOrType-span (DefType pi x k tp) = erased-var-span pi x ll-type ≫span erased-kind-spans k ≫span erased-type-spans tp

get-defTermOrType-pi-v : defTermOrType → (posinfo × var)
get-defTermOrType-pi-v (DefTerm pi x _ _) = pi , x
get-defTermOrType-pi-v _ = "" , ""

erased-tk-span : tk → spanM ⊤
erased-tk-span (Tkt tp) = erased-type-spans tp
erased-tk-span (Tkk k) = erased-kind-spans k


{-# TERMINATING #-}
erased-term-spans (App t me t') =
  put-span (term-start-pos t) (term-end-pos t') ll-term [] ≫span
  erased-term-spans t ≫span erased-term-spans t'
erased-term-spans (Beta pi ot) = optTerm-span ot
erased-term-spans (Hole pi) = inc-span pi ll-term []
erased-term-spans (Lam pi l pi' v oc t) =
  put-span pi (term-end-pos t) ll-term (binder-data-const :: []) ≫span
  get-ctxt (λ Γ →
    let Γ' = ctxt-var-decl (inc-pi pi') v Γ in
      set-ctxt Γ' ≫span
      erased-var-span pi' v ll-term ≫span
      erased-term-spans t ≫span
      set-ctxt Γ)
erased-term-spans (Let pi dtt t) =
  get-ctxt (λ Γ →
    put-span pi (term-end-pos t) ll-term (binder-data-const :: bound-data dtt Γ :: []) ≫span
    let pi-v = get-defTermOrType-pi-v dtt in
      let Γ' = ctxt-var-decl (inc-pi (fst pi-v)) (snd pi-v) Γ in
        set-ctxt Γ' ≫span
        defTermOrType-span dtt ≫span
        erased-term-spans t ≫span
        set-ctxt Γ)
erased-term-spans (Parens pi t pi') = erased-term-spans t
erased-term-spans (Var pi v) = erased-var-span pi v ll-term
erased-term-spans t = error-spans ("Unknown term: " ^ (ParseTreeToString (parsed-term t))
  ^ ", " ^ (to-string (new-ctxt "" "") t) ^ " (erased-spans.agda)")

erased-type-spans (Abs pi b pi' v t-k tp) =
  put-span pi (type-end-pos tp) ll-type [] ≫span
  erased-tk-span t-k ≫span
  get-ctxt (λ Γ →
    let Γ' = ctxt-var-decl (inc-pi pi') v Γ in
      set-ctxt Γ' ≫span
      erased-var-span pi' v ll-type ≫span
      erased-type-spans tp ≫span
      set-ctxt Γ)
erased-type-spans (IotaEx pi i pi' v ot tp) =
  put-span pi (type-end-pos tp) ll-type [] ≫span
  erased-var-span pi' v ll-type ≫span
  optType-span ot ≫span
  erased-type-spans tp
erased-type-spans (Lft pi pi' v t lt) =
  put-span pi (term-end-pos t) ll-type [] ≫span
  erased-var-span pi v ll-type ≫span
  erased-term-spans t
erased-type-spans (NoSpans tp pi) = spanMok
erased-type-spans (TpApp tp tp') =
  put-span (type-start-pos tp) (type-end-pos tp') ll-type [] ≫span
  erased-type-spans tp ≫span
  erased-type-spans tp'
erased-type-spans (TpAppt tp t) =
  put-span (type-start-pos tp) (term-end-pos t) ll-type [] ≫span
  erased-type-spans tp ≫span erased-term-spans t
erased-type-spans (TpArrow tp at tp') =
  put-span (type-start-pos tp) (type-end-pos tp') ll-type [] ≫span
  erased-type-spans tp ≫span
  erased-type-spans tp'
erased-type-spans (TpEq t t') =
  put-span (term-start-pos t) (term-end-pos t') ll-type [] ≫span
  erased-term-spans t ≫span
  erased-term-spans t'
erased-type-spans (TpHole pi) = inc-span pi ll-type []
erased-type-spans (TpLambda pi pi' v t-k tp) =
  put-span pi (type-end-pos tp) ll-type [] ≫span
  erased-tk-span t-k ≫span
  get-ctxt (λ Γ →
    let Γ' = ctxt-var-decl (inc-pi pi') v Γ in
      set-ctxt Γ' ≫span
      erased-var-span pi' v ll-type ≫span
      erased-type-spans tp ≫span
      set-ctxt Γ)
erased-type-spans (TpParens pi tp pi') = erased-type-spans tp
erased-type-spans (TpVar pi v) = erased-var-span pi v ll-type


erased-kind-spans (KndArrow k k') = put-span (kind-start-pos k) (kind-end-pos k') ll-kind [] ≫span
  erased-kind-spans k ≫span erased-kind-spans k'
erased-kind-spans (KndParens pi k pi') = erased-kind-spans k
erased-kind-spans (KndPi pi pi' v t-k k) =
  put-span pi (kind-end-pos k) ll-kind [] ≫span
  get-ctxt (λ Γ →
    let Γ' = ctxt-var-decl (inc-pi pi') v Γ in
      set-ctxt Γ' ≫span
      erased-var-span pi' v ll-kind ≫span
      erased-tk-span t-k ≫span
      erased-kind-spans k ≫span
      set-ctxt Γ)
erased-kind-spans (KndTpArrow tp k) =
  put-span (type-start-pos tp) (kind-end-pos k) ll-kind [] ≫span
  erased-type-spans tp ≫span
  erased-kind-spans k
erased-kind-spans (KndVar pi kv as) = erased-var-span pi kv ll-kind
erased-kind-spans (Star pi) = inc-span pi ll-kind []
