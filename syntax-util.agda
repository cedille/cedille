module syntax-util where

open import lib
open import cedille-types

-- NB: \GTH is for Θ, while \Gth is for θ.  The characters are imperceptibly different at usual font size.

castDir-to-string : castDir → string
castDir-to-string checkCast = "⇐"
castDir-to-string synthCast = "⇒"

kind-to-string : kind → string
tk-to-string : tk → string
type-to-string : type → string
term-to-string : term → string
ip-to-string : ip → string
al-to-string : al → string
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
type-to-string (Lft x t tp) = "↑ " ^ x ^ " . " ^ term-to-string t ^ " : " ^ liftingType-to-string tp 
type-to-string (TpApp t t₁) = "(" ^ type-to-string t ^ " · " ^ type-to-string t₁ ^ ")"
type-to-string (TpAppt t x) = "(" ^ type-to-string t ^ " " ^ term-to-string x ^ ")"
type-to-string (TpParens x) = type-to-string x
type-to-string (TpVar x) = x
type-to-string U = "𝓤"

ip-to-string Iota = "ι"
ip-to-string Pi = "Π"

al-to-string All = "∀"
al-to-string Lambda = "λ"

term-to-string (App t t₁) = "(" ^ term-to-string t ^ " " ^ term-to-string t₁ ^ ")"
term-to-string (Var x) = x
term-to-string (Lam x x₁) = "(λ " ^ x ^ " . " ^ term-to-string x₁ ^ ")"
term-to-string (Parens x) = term-to-string x

ctorset-to-string (Add x x₁ θ) = term-to-string x ^ " ∈ " ^ type-to-string x₁ ^ " , " ^ ctorset-to-string θ
ctorset-to-string Empty = "·"

liftingType-to-string (LiftArrow t t₁) = "(" ^ liftingType-to-string t ^ " → " ^ liftingType-to-string t₁ ^ ")"
liftingType-to-string (LiftParens t) = liftingType-to-string t
liftingType-to-string (LiftPi x x₁ t) = "(Π " ^ x ^ " : " ^ type-to-string x₁ ^ " . " ^ liftingType-to-string t ^ ")"
liftingType-to-string (LiftVar x) = x

evidence-to-string : evidence → string
evidence-to-string Beta = "β"
evidence-to-string (Cast e d e₁) = "(χ " ^ evidence-to-string e ^ (castDir-to-string d) ^ evidence-to-string e₁ ^ ")"
evidence-to-string Check = "✓"
evidence-to-string (Ctor e x) = "unimplemented"
evidence-to-string (Ctora x) = "unimplemented"
evidence-to-string (Eapp e e₁) = "(" ^ evidence-to-string e ^ " " ^ evidence-to-string e₁ ^ ")"
evidence-to-string (Eappk e t) = "〈" ^ evidence-to-string e ^ " " ^ type-to-string t ^ "〉"
evidence-to-string (Eappt e t) = "〈" ^ evidence-to-string e ^ " " ^ term-to-string t ^ "〉"
evidence-to-string (Earrow e e₁) = "(" ^ evidence-to-string e ^ " ⇒ " ^ evidence-to-string e₁ ^ ")"
evidence-to-string (Ehole x) = "unimplemented"
evidence-to-string (EholeNamed x x₁) = "unimplemented"
evidence-to-string (Elift x e e') = "(↑ " ^ x ^ " . " ^ evidence-to-string e ^ " : " ^ evidence-to-string e' ^ ")"
evidence-to-string (Elet x e) = "unimplemented"
evidence-to-string (Enu x x₁ e e₁ e₂ e₃) = "unimplemented"
evidence-to-string (Eparens e) = evidence-to-string e
evidence-to-string (Eprint x e) = "unimplemented"
evidence-to-string (Evar x) = x
evidence-to-string (Pair e e₁) = "unimplemented"
evidence-to-string (Proj e x) = "unimplemented"
evidence-to-string (Sym e) = "unimplemented"
evidence-to-string (Trans e e₁) = "unimplemented"
evidence-to-string (Xi x x₁ e) = "unimplemented"

-- tt means positive, ff means negative.
occurs-only-polarity : var → 𝔹 → type → 𝔹
occurs-only-polarity v p t = tt

check-ctors : var → ctorset → maybe string
check-ctors v c = nothing

-- the stringset tells which variables are bound, and the 𝕃 string is
-- an accumulator argument.
free-varsh : stringset → 𝕃 string → term → 𝕃 string
free-varsh b f (Var x) = if trie-contains b x then f else (x :: f)
free-varsh b f (App t1 t2) = free-varsh b (free-varsh b f t1) t2
free-varsh b f (Lam x t) = free-varsh (stringset-insert b x) f t
free-varsh b f (Parens t) = free-varsh b f t

free-vars : term → 𝕃 string
free-vars t = free-varsh empty-stringset [] t 

get-defined-symbol : def → string
get-defined-symbol (Edefine x _ _ _) = x
get-defined-symbol (Kdefine x _ _) = x
get-defined-symbol (Tdefine x _) = x

lift-liftingType : liftingType → type
lift-liftingType (LiftVar x) = TpVar x
lift-liftingType (LiftArrow ltp1 ltp2) = TpArrow (lift-liftingType ltp1) (lift-liftingType ltp2)
lift-liftingType (LiftPi x tp ltp) = AbsTp1 Pi x tp (lift-liftingType ltp)
lift-liftingType (LiftParens ltp) = lift-liftingType ltp

lift-to-kind : liftingType → kind
lift-to-kind (LiftVar x) = Star
lift-to-kind (LiftArrow ltp1 ltp2) = KndArrow (lift-to-kind ltp1) (lift-to-kind ltp2)
lift-to-kind (LiftPi x tp ltp) = KndPi x (Tkt tp) (lift-to-kind ltp)
lift-to-kind (LiftParens ltp) = lift-to-kind ltp

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