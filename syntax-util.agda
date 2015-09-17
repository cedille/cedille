module syntax-util where

open import lib
open import cedille-types
open import rename

-- NB: \GTH is for Θ, while \Gth is for θ.  The characters are imperceptibly different at usual font size.

castDir-to-string : castDir → string
castDir-to-string checkCast = " ⇐ "
castDir-to-string synthCast = " ⇒ "

showCtxt-to-string : showCtxt → string
showCtxt-to-string showCtxtNo = ""
showCtxt-to-string showCtxtYes = "!"

ip-to-string : ip → string
ip-to-string Iota = "ι"
ip-to-string Pi = "Π"

al-to-string : al → string
al-to-string All = "∀"
al-to-string Lambda = "λ"

kind-to-string : renamectxt → kind → string
tk-to-string : renamectxt → tk → string
type-to-string : renamectxt → type → string
term-to-string : renamectxt → term → string
ctorset-to-string : renamectxt → ctorset → string
liftingType-to-string : renamectxt → liftingType → string

kind-to-string r (KndArrow k k') = "(" ^ kind-to-string r k ^ " → " ^ kind-to-string r k' ^ ")"
kind-to-string r (KndParens k) = kind-to-string r k
kind-to-string r (KndPi x u k) = let r' = trie-remove r x in 
                                   "(Π " ^ x ^ " : " ^ tk-to-string r' u ^ " . " ^ kind-to-string r' k ^ ")"
kind-to-string r (KndTpArrow x k) = "(" ^ type-to-string r x ^ " → " ^ kind-to-string r k ^ ")"
kind-to-string r (KndVar x) = x
kind-to-string r Star = "★"

tk-to-string r (Tkk k) = kind-to-string r k
tk-to-string r (Tkt t) = type-to-string r t

type-to-string r (AbsTp1 b x t1 t2) = 
  let r' = trie-remove r x in
    "(" ^ (ip-to-string b) ^ " " ^ x ^ " : " ^ type-to-string r t1 ^ " . " ^ type-to-string r' t2 ^ ")"
type-to-string r (AbsTp2 b x t1 t2) = 
  let r' = trie-remove r x in
    "(" ^ (al-to-string b) ^ " " ^ x ^ " : " ^ tk-to-string r t1 ^ " . " ^ type-to-string r' t2 ^ ")"
type-to-string r (Nu x k Θ t) = 
  let r' = trie-remove r x in
    "(ν" ^ " " ^ x ^ " : " ^ kind-to-string r k ^ " | " ^ ctorset-to-string r' Θ ^ " . " ^ type-to-string r' t ^ ")"
type-to-string r (TpArrow x t) = "(" ^ type-to-string r x ^ " → " ^  type-to-string r t ^ ")"
type-to-string r (Lft t tp) = "↑ " ^ term-to-string r t ^ " : " ^ liftingType-to-string r tp 
type-to-string r (TpApp t t₁) = "(" ^ type-to-string r t ^ " · " ^ type-to-string r t₁ ^ ")"
type-to-string r (TpAppt t x) = "(" ^ type-to-string r t ^ " " ^ term-to-string r x ^ ")"
type-to-string r (TpParens x) = type-to-string r x
type-to-string r (TpEq t1 t2) = "(" ^ term-to-string r t1 ^ " ≃ " ^ term-to-string r t2 ^ ")"
type-to-string r (TpVar x) = renamectxt-rep r x
type-to-string r U = "𝓤"

term-to-string r (App t t₁) = "(" ^ term-to-string r t ^ " " ^ term-to-string r t₁ ^ ")"
term-to-string r (Var x) = renamectxt-rep r x
term-to-string r (Lam x x₁) = 
 let r' = trie-remove r x in
  "(λ " ^ x ^ " . " ^ term-to-string r' x₁ ^ ")"
term-to-string r (Parens x) = term-to-string r x

ctorset-to-string r (Add x x₁ θ) = term-to-string r x ^ " ∈ " ^ type-to-string r x₁ ^ " , " ^ ctorset-to-string r θ
ctorset-to-string r Empty = "·"

liftingType-to-string r (LiftArrow t t₁) = "(" ^ liftingType-to-string r t ^ " → " ^ liftingType-to-string r t₁ ^ ")"
liftingType-to-string r (LiftTpArrow t t₁) = "(" ^ type-to-string r t ^ " → " ^ liftingType-to-string r t₁ ^ ")"
liftingType-to-string r (LiftParens t) = liftingType-to-string r t
liftingType-to-string r (LiftPi x x₁ t) = 
  let r' = trie-remove r x in
    "(Π " ^ x ^ " : " ^ type-to-string r x₁ ^ " . " ^ liftingType-to-string r' t ^ ")"
liftingType-to-string r LiftStar = "☆"

evidence-to-string : renamectxt → evidence → string
evidence-to-string r Beta = "β"
evidence-to-string r BetaAll = "β*"
evidence-to-string r (Rbeta e t e') = "(rβ " ^ evidence-to-string r e ^ " " ^ term-to-string r t ^ " ⇒ " ^ evidence-to-string r e'  ^ ")"
evidence-to-string r (RbetaLift n) = "(rβ↑ " ^ n ^ ")"
evidence-to-string r (EliftCong e) = "(↑c " ^ evidence-to-string r e ^ ")"
evidence-to-string r (LamCong e) = "(ξ " ^ evidence-to-string r e ^ ")"
evidence-to-string r (EtaAll e t) = "(η∀ " ^ evidence-to-string r e ^ " " ^ term-to-string r t ^ ")"
evidence-to-string r (EtaLift n) = "(η↑ " ^ n ^ ")"
evidence-to-string r (Cast e d e₁) = "(χ " ^ evidence-to-string r e ^ (castDir-to-string d) ^ evidence-to-string r e₁ ^ ")"
evidence-to-string r Check = "✓"
evidence-to-string r (Ctor e x) = "(ζ " ^ evidence-to-string r e ^ " : " ^ type-to-string r x ^ ")"
evidence-to-string r (Ctora x) = "(ζ " ^ x ^ ")"
evidence-to-string r (Eapp e e₁) = "(" ^ evidence-to-string r e ^ " " ^ evidence-to-string r e₁ ^ ")"
evidence-to-string r (Eappk e t) = "〈" ^ evidence-to-string r e ^ " " ^ type-to-string r t ^ "〉"
evidence-to-string r (Eappt e t) = "{" ^ evidence-to-string r e ^ " " ^ term-to-string r t ^ "}"
evidence-to-string r (Earrow e e₁) = "(" ^ evidence-to-string r e ^ " ⇒ " ^ evidence-to-string r e₁ ^ ")"
evidence-to-string r (Ehole x) = "●" ^ showCtxt-to-string x 
evidence-to-string r EholeSilent = "●."
evidence-to-string r (EholeNamed x x₁) = "●" ^ showCtxt-to-string x ^ x₁
evidence-to-string r (Elift x e e') = "(↑ " ^ x ^ " . " ^ evidence-to-string r e ^ " : " ^ evidence-to-string r e' ^ ")"
evidence-to-string r (Elet x e) = "unimplemented"
evidence-to-string r (Enu x x₁ e e₁ e₂ e₃) = "unimplemented"
evidence-to-string r (Eparens e) = evidence-to-string r e
evidence-to-string r (Eprint x e) = "unimplemented"
evidence-to-string r (Evar x) = x
evidence-to-string r (Pair e e₁) = "unimplemented"
evidence-to-string r (Proj e x) = "unimplemented"
evidence-to-string r (Sym e) = "(~ " ^ evidence-to-string r e ^ ")"
evidence-to-string r (Trans e e₁) = "(" ^ evidence-to-string r e ^ " · " ^ evidence-to-string r e₁ ^ ")"
evidence-to-string r (Xi x (EclassSome x₁) e) = "(ξ " ^ x ^ " : " ^ evidence-to-string r x₁ ^ " . " ^ evidence-to-string r e ^ ")"
evidence-to-string r (Xi x EclassNone e) = "(ξ " ^ x ^ " . " ^ evidence-to-string r e ^ ")"


-- tt means positive, ff means negative.
occurs-only-polarity : var → 𝔹 → type → 𝔹
occurs-only-polarity v p t = tt

check-ctors : var → ctorset → maybe string
check-ctors v c = nothing

get-defined-symbol : def → string
get-defined-symbol (Edefine x _ _ _) = x
get-defined-symbol (Kdefine x _ _) = x
get-defined-symbol (Tdefine x _) = x

liftingType-to-type : var → liftingType → type
liftingType-to-type v LiftStar = TpVar v
liftingType-to-type v (LiftArrow ltp1 ltp2) = TpArrow (liftingType-to-type v ltp1) (liftingType-to-type v ltp2)
liftingType-to-type v (LiftTpArrow tp ltp) = TpArrow tp (liftingType-to-type v ltp)
liftingType-to-type v (LiftPi x tp ltp) = AbsTp1 Pi x tp (liftingType-to-type v ltp)
liftingType-to-type v (LiftParens ltp) = liftingType-to-type v ltp

newline-sep-if : string → string → string
newline-sep-if x x' = if (x =string "") || (x' =string "") then "" else "\n"

spine-formh : term → term × 𝕃 term
spine-formh (Parens t) = spine-formh t
spine-formh (App t1 t2) with spine-formh t1
spine-formh (App t1 t2) | h , args = h , (t2 :: args)
spine-formh (Lam x t) = Lam x t , []
spine-formh (Var x) = Var x , []

spine-form : term → term × 𝕃 term
spine-form t with spine-formh t
spine-form t | h , args = h , reverse args

app-spine : term → 𝕃 term → term
app-spine h (arg :: args) = app-spine (App h arg) args
app-spine h [] = h

type-app-spine : type → 𝕃 type → type
type-app-spine h (arg :: args) = type-app-spine (TpApp h arg) args
type-app-spine h [] = h

lambdas : 𝕃 var → term → term
lambdas [] t = t
lambdas (x :: xs) t = (Lam x (lambdas xs t))

lift-arrows : 𝕃 liftingType → liftingType → liftingType
lift-arrows [] t = t
lift-arrows (u :: us) t = LiftArrow u (lift-arrows us t)

-- try to remove n type arguments from the given type, returning the remaining head term and the arguments
remove-type-args : (n : ℕ) → type → maybe (type × (𝕍 type n))
remove-type-args n (TpParens tp) = remove-type-args n tp
remove-type-args 0 h = just (h , [] )
remove-type-args (suc n) (TpApp t1 t2) with remove-type-args n t1
remove-type-args (suc n) (TpApp t1 t2) | nothing = nothing
remove-type-args (suc n) (TpApp t1 t2) | just (h , args ) = just (h , t2 :: args )
remove-type-args (suc n) tp = nothing 

-- try to remove n lambda-bound vars from the term, returning the vars and the remaining body
remove-lam-vars : (n : ℕ) → term → maybe ((𝕍 string n) × term)
remove-lam-vars n (Parens t) = remove-lam-vars n t
remove-lam-vars 0 t = just ([] , t)
remove-lam-vars (suc n) (Lam x t) with remove-lam-vars n t
remove-lam-vars (suc n) (Lam x t) | nothing = nothing
remove-lam-vars (suc n) (Lam x t) | just (vs , b) = just (x :: vs , b)
remove-lam-vars (suc n) trm = nothing

remove-inputs-liftingType : (n : ℕ) → liftingType → maybe ((𝕍 liftingType n) × liftingType)
remove-inputs-liftingType n (LiftParens l) = remove-inputs-liftingType n l
remove-inputs-liftingType 0 l = just ([] , l)
remove-inputs-liftingType (suc n) (LiftArrow ltp1 ltp2) with remove-inputs-liftingType n ltp2
remove-inputs-liftingType (suc n) (LiftArrow ltp1 ltp2) | nothing = nothing
remove-inputs-liftingType (suc n) (LiftArrow ltp1 ltp2) | just (ds , r) = just (ltp1 :: ds , r)
remove-inputs-liftingType (suc n) ltp = nothing