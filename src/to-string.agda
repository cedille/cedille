module to-string where

open import lib
open import cedille-types
open import syntax-util

binder-to-string : binder → string
binder-to-string All = "∀"
binder-to-string Pi = "Π"

maybeErased-to-string : maybeErased → string
maybeErased-to-string Erased = "-"
maybeErased-to-string NotErased = ""

lam-to-string : lam → string
lam-to-string ErasedLambda = "Λ"
lam-to-string KeptLambda = "λ"

leftRight-to-string : leftRight → string
leftRight-to-string Left = "l"
leftRight-to-string Right = "r"
leftRight-to-string Both = ""

vars-to-string : vars → string
vars-to-string (VarsStart v) = v
vars-to-string (VarsNext v vs) = v ^ " " ^ vars-to-string vs

theta-to-string : theta → string
theta-to-string Abstract = "θ"
theta-to-string AbstractEq = "θ+"
theta-to-string (AbstractVars vs) = "θ<" ^ vars-to-string vs ^ ">"

maybeMinus-to-string : maybeMinus → string
maybeMinus-to-string EpsHnf = ""
maybeMinus-to-string EpsHanf = "-"

type-to-string : 𝔹 → type → string
term-to-string : 𝔹 → term → string
kind-to-string : 𝔹 → kind → string
lterms-to-stringh : lterms → string
type-to-stringh : {ed : exprd} → 𝔹 → ⟦ ed ⟧ → type → string
term-to-stringh : {ed : exprd} → 𝔹 → ⟦ ed ⟧ → term → string
kind-to-stringh : {ed : exprd} → 𝔹 → ⟦ ed ⟧ → kind → string
optClass-to-string : optClass → string
tk-to-string : tk → string
liftingType-to-string : liftingType → string
liftingType-to-stringh : {ed : exprd} → ⟦ ed ⟧ → liftingType → string
maybeAtype-to-string : maybeAtype → string

parens-unless : 𝔹 → 𝔹 → string → string
parens-unless toplevel locally-not-needed s =
  if toplevel || locally-not-needed then s else ("(" ^ s ^ ")")

term-to-string toplevel t = term-to-stringh toplevel star t
type-to-string toplevel tp = type-to-stringh toplevel star tp
kind-to-string toplevel k = kind-to-stringh toplevel star k
liftingType-to-string l = liftingType-to-stringh star l

term-to-stringh toplevel  p (App t x t') = 
  parens-unless toplevel (is-app p) (term-to-stringh ff (App t x t') t ^ " " ^ (maybeErased-to-string x) ^ term-to-string ff t')
term-to-stringh toplevel p (AppTp t tp) = parens-unless toplevel (is-app p) (term-to-stringh ff (AppTp t tp) t ^ " · " ^ type-to-string ff tp)
term-to-stringh toplevel p (Hole _) = "●"
term-to-stringh toplevel p (Lam pi l pi' x o t) = 
  parens-unless toplevel (is-abs p) (lam-to-string l ^ " " ^ x ^ optClass-to-string o ^ " . " ^ term-to-stringh ff (Lam pi l pi' x o t) t)
term-to-stringh toplevel p (Parens _ t _) = term-to-string toplevel t
term-to-stringh toplevel p (Var _ x) = x
term-to-stringh toplevel p (Beta _) = "β"
term-to-stringh toplevel p (Delta _ t) = "(δ" ^ " " ^ term-to-string ff t ^ ")"
term-to-stringh toplevel p (PiInj _ n t) = "(π" ^ n ^ " " ^ term-to-string ff t ^ ")"
term-to-stringh toplevel p (Epsilon _ lr m t) = "(ε" ^ leftRight-to-string lr ^ maybeMinus-to-string m ^ " " ^ term-to-string ff t ^ ")"
term-to-stringh toplevel p (Sigma _ t) = "(ς " ^ term-to-string ff t ^ ")"
term-to-stringh toplevel p (Theta _ u t ts) = "(" ^ theta-to-string u ^ " " ^ term-to-string ff t ^ lterms-to-stringh ts ^ ")"
term-to-stringh toplevel p (Rho _ t t') = "(ρ " ^ term-to-string ff t ^ " - " ^ term-to-string ff t' ^ ")"
term-to-stringh toplevel p (Chi _ T t') = "(χ " ^ maybeAtype-to-string T ^ " - " ^ term-to-string ff t' ^ ")"

type-to-stringh toplevel p (Abs pi b pi' x t t') = 
  parens-unless toplevel (is-abs p)
    (binder-to-string b ^ " " ^ x ^ " : " ^ tk-to-string t ^ " . " ^ type-to-stringh ff (Abs pi b pi' x t t') t')
type-to-stringh toplevel p (TpLambda pi pi' x tk t) = 
  parens-unless toplevel (is-abs p) ("λ " ^ x ^ " : " ^ tk-to-string tk ^ " . " ^ type-to-stringh ff (TpLambda pi pi' x tk t) t )
type-to-stringh toplevel p (Iota pi x m t) = parens-unless toplevel (is-abs p) ("ι " ^ x ^ optClass-to-string m ^ " . " 
                                  ^ type-to-stringh ff (Iota pi x m t) t)
type-to-stringh toplevel p (Lft _ _ X x x₁) = "(↑ " ^ X ^ " . " ^ term-to-string ff x ^ " : " ^ liftingType-to-string x₁ ^ ")"
type-to-stringh toplevel p (TpApp t t₁) = parens-unless toplevel (is-app p) (type-to-stringh ff (TpApp t t₁) t ^ " · " ^ type-to-string ff t₁)
type-to-stringh toplevel p (TpAppt t t') = parens-unless toplevel (is-app p) (type-to-stringh ff (TpAppt t t') t ^ " " ^ term-to-string ff t')
type-to-stringh toplevel p (TpArrow x t) =
  parens-unless toplevel (is-arrow p) (type-to-string ff x ^ " → " ^  type-to-stringh ff (TpArrow x t) t)
type-to-stringh toplevel p (TpEq t1 t2) = "(" ^ term-to-string ff t1 ^ " ≃ " ^ term-to-string ff t2 ^ ")"
type-to-stringh toplevel p (TpParens _ t _) = type-to-string toplevel t
type-to-stringh toplevel p (TpVar _ x) = x
type-to-stringh toplevel p (NoSpans t _) = type-to-string ff t

kind-to-stringh toplevel p (KndArrow k k') =
  parens-unless toplevel (is-arrow p) (kind-to-string ff k ^ " → " ^ kind-to-stringh ff (KndArrow k k') k')
kind-to-stringh toplevel p (KndParens _ k _) = kind-to-string toplevel k
kind-to-stringh toplevel p (KndPi pi pi' x u k) = 
  parens-unless toplevel (is-abs p) ("Π " ^ x ^ " : " ^ tk-to-string u ^ " . " ^ kind-to-stringh ff (KndPi pi pi' x u k) k )
kind-to-stringh toplevel p (KndTpArrow x k) =
  parens-unless toplevel (is-arrow p) (type-to-string ff x ^ " → " ^ kind-to-stringh ff (KndTpArrow x k) k)
kind-to-stringh toplevel p (KndVar _ x) = x
kind-to-stringh toplevel p (Star _) = "★"

liftingType-to-stringh p (LiftArrow t t₁) = 
  parens-unless ff (is-arrow p) (liftingType-to-string t ^ " → " ^ liftingType-to-stringh (LiftArrow t t₁) t₁ )
liftingType-to-stringh p (LiftTpArrow t t₁) = 
  parens-unless ff (is-arrow p) (type-to-string ff t ^ " → " ^ liftingType-to-stringh (LiftTpArrow t t₁) t₁ )
liftingType-to-stringh p (LiftParens _ t _) = liftingType-to-string t
liftingType-to-stringh p (LiftPi pi x x₁ t) = 
  parens-unless ff (is-abs p) ("Π " ^ x ^ " : " ^ type-to-string ff x₁ ^ " . " ^ liftingType-to-stringh (LiftPi pi x x₁ t) t)
liftingType-to-stringh p (LiftStar _) = "☆"

optClass-to-string NoClass = ""
optClass-to-string (SomeClass x) = " : " ^ tk-to-string x

tk-to-string (Tkk k) = kind-to-string ff k
tk-to-string (Tkt t) = type-to-string ff t

lterms-to-stringh (LtermsNil _) = ""
lterms-to-stringh (LtermsCons t ts) = " " ^ term-to-string ff t ^ lterms-to-stringh ts

maybeAtype-to-string NoAtype = ""
maybeAtype-to-string (Atype T) = type-to-string ff T

to-string : {ed : exprd} → ⟦ ed ⟧ → string
to-string{TERM} = term-to-string tt
to-string{TYPE} = type-to-string tt
to-string{KIND} = kind-to-string tt
to-string{LIFTINGTYPE} = liftingType-to-string 

to-string-if : {ed : exprd} → maybe (⟦ ed ⟧) → string
to-string-if (just e) = to-string e
to-string-if nothing = "[nothing]"
