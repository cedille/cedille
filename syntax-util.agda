module syntax-util where

open import lib
open import cedille-types
open import rename

-- NB: \GTH is for Θ, while \Gth is for θ.  The characters are imperceptibly different at usual font size.

castDir-to-string : castDir → string
castDir-to-string checkCast = "⇐"
castDir-to-string synthCast = "⇒"

showCtxt-to-string : showCtxt → string
showCtxt-to-string showCtxtNo = ""
showCtxt-to-string showCtxtYes = "!"

ip-to-string : ip → string
ip-to-string Iota = "ι"
ip-to-string Pi = "Π"

al-to-string : al → string
al-to-string All = "∀"
al-to-string Lambda = "λ"

kind-to-string : kind → string
tk-to-string : tk → string
type-to-string : type → string
term-to-string : term → string
ctorset-to-string : ctorset → string
liftingType-to-string : liftingType → string

kind-to-string (KndArrow k k') = "(" ^ kind-to-string k ^ " → " ^ kind-to-string k' ^ ")"
kind-to-string (KndParens k) = kind-to-string k
kind-to-string (KndPi x u k) = "(Π " ^ x ^ " : " ^ tk-to-string u ^ " . " ^ kind-to-string k ^ ")"
kind-to-string (KndTpArrow x k) = "(" ^ type-to-string x ^ " → " ^ kind-to-string k ^ ")"
kind-to-string (KndVar x) = x
kind-to-string Star = "★"

tk-to-string (Tkk k) = kind-to-string k
tk-to-string (Tkt t) = type-to-string t

type-to-string (AbsTp1 b x t1 t2) = "(" ^ (ip-to-string b) ^ " " ^ x ^ " : " ^ type-to-string t1 ^ " . " ^ type-to-string t2 ^ ")"
type-to-string (AbsTp2 b x t1 t2) = "(" ^ (al-to-string b) ^ " " ^ x ^ " : " ^ tk-to-string t1 ^ " . " ^ type-to-string t2 ^ ")"
type-to-string (Nu x k Θ t) = "(ν" ^ " " ^ x ^ " : " ^ kind-to-string k ^ " | " ^ ctorset-to-string Θ ^ " . " ^ type-to-string t ^ ")"
type-to-string (TpArrow x t) = "(" ^ type-to-string x ^ " → " ^  type-to-string t ^ ")"
type-to-string (Lft t tp) = "↑ " ^ term-to-string t ^ " : " ^ liftingType-to-string tp 
type-to-string (TpApp t t₁) = "(" ^ type-to-string t ^ " · " ^ type-to-string t₁ ^ ")"
type-to-string (TpAppt t x) = "(" ^ type-to-string t ^ " " ^ term-to-string x ^ ")"
type-to-string (TpParens x) = type-to-string x
type-to-string (TpVar x) = x
type-to-string U = "𝓤"

term-to-string (App t t₁) = "(" ^ term-to-string t ^ " " ^ term-to-string t₁ ^ ")"
term-to-string (Var x) = x
term-to-string (Lam x x₁) = "(λ " ^ x ^ " . " ^ term-to-string x₁ ^ ")"
term-to-string (Parens x) = term-to-string x

ctorset-to-string (Add x x₁ θ) = term-to-string x ^ " ∈ " ^ type-to-string x₁ ^ " , " ^ ctorset-to-string θ
ctorset-to-string Empty = "·"

liftingType-to-string (LiftArrow t t₁) = "(" ^ liftingType-to-string t ^ " → " ^ liftingType-to-string t₁ ^ ")"
liftingType-to-string (LiftTpArrow t t₁) = "(" ^ type-to-string t ^ " → " ^ liftingType-to-string t₁ ^ ")"
liftingType-to-string (LiftParens t) = liftingType-to-string t
liftingType-to-string (LiftPi x x₁ t) = "(Π " ^ x ^ " : " ^ type-to-string x₁ ^ " . " ^ liftingType-to-string t ^ ")"
liftingType-to-string LiftStar = "☆"

evidence-to-string : evidence → string
evidence-to-string Beta = "β"
evidence-to-string (Rbeta e t e') = "(rβ " ^ evidence-to-string e ^ " " ^ term-to-string t ^ " ⇒ " ^ evidence-to-string e'  ^ ")"
evidence-to-string (RbetaLift n) = "(rβ↑ " ^ n ^ ")"
evidence-to-string (EliftCong e) = "(↑c " ^ evidence-to-string e ^ ")"
evidence-to-string (LamCong e) = "(ξ " ^ evidence-to-string e ^ ")"
evidence-to-string (EtaAll e t) = "(η∀ " ^ evidence-to-string e ^ " " ^ term-to-string t ^ ")"
evidence-to-string (EtaLift n) = "(η↑ " ^ n ^ ")"
evidence-to-string (Cast e d e₁) = "(χ " ^ evidence-to-string e ^ (castDir-to-string d) ^ evidence-to-string e₁ ^ ")"
evidence-to-string Check = "✓"
evidence-to-string (Ctor e x) = "(ζ " ^ evidence-to-string e ^ " : " ^ type-to-string x ^ ")"
evidence-to-string (Ctora x) = "(ζ " ^ x ^ ")"
evidence-to-string (Eapp e e₁) = "(" ^ evidence-to-string e ^ " " ^ evidence-to-string e₁ ^ ")"
evidence-to-string (Eappk e t) = "〈" ^ evidence-to-string e ^ " " ^ type-to-string t ^ "〉"
evidence-to-string (Eappt e t) = "{" ^ evidence-to-string e ^ " " ^ term-to-string t ^ "}"
evidence-to-string (Earrow e e₁) = "(" ^ evidence-to-string e ^ " ⇒ " ^ evidence-to-string e₁ ^ ")"
evidence-to-string (Ehole x) = "●" ^ showCtxt-to-string x 
evidence-to-string (EholeNamed x x₁) = "unimplemented"
evidence-to-string (Elift x e e') = "(↑ " ^ x ^ " . " ^ evidence-to-string e ^ " : " ^ evidence-to-string e' ^ ")"
evidence-to-string (Elet x e) = "unimplemented"
evidence-to-string (Enu x x₁ e e₁ e₂ e₃) = "unimplemented"
evidence-to-string (Eparens e) = evidence-to-string e
evidence-to-string (Eprint x e) = "unimplemented"
evidence-to-string (Evar x) = x
evidence-to-string (Pair e e₁) = "unimplemented"
evidence-to-string (Proj e x) = "unimplemented"
evidence-to-string (Sym e) = "(~ " ^ evidence-to-string e ^ ")"
evidence-to-string (Trans e e₁) = "(" ^ evidence-to-string e ^ " · " ^ evidence-to-string e₁ ^ ")"
evidence-to-string (Xi x (EclassSome x₁) e) = "(ξ " ^ x ^ " : " ^ evidence-to-string x₁ ^ " . " ^ evidence-to-string e ^ ")"
evidence-to-string (Xi x EclassNone e) = "(ξ " ^ x ^ " . " ^ evidence-to-string e ^ ")"


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