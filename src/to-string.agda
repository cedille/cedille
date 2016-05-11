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

type-to-string : type → string
term-to-string : term → string
kind-to-string : kind → string
lterms-to-stringh : lterms → string
type-to-stringh : {ed : exprd} → ⟦ ed ⟧ → type → string
term-to-stringh : {ed : exprd} → ⟦ ed ⟧ → term → string
kind-to-stringh : {ed : exprd} → ⟦ ed ⟧ → kind → string
optClass-to-string : optClass → string
tk-to-string : tk → string
liftingType-to-string : liftingType → string
liftingType-to-stringh : {ed : exprd} → ⟦ ed ⟧ → liftingType → string
maybeAtype-to-string : maybeAtype → string

parens-unless : 𝔹 → string → string
parens-unless ff s = "(" ^ s ^ ")"
parens-unless tt s = s

term-to-string t = term-to-stringh star t
type-to-string tp = type-to-stringh star tp
kind-to-string k = kind-to-stringh star k
liftingType-to-string l = liftingType-to-stringh star l

term-to-stringh p (App t x t') = 
  parens-unless (is-app p) (term-to-stringh (App t x t') t ^ " " ^ (maybeErased-to-string x) ^ term-to-string t')
term-to-stringh p (AppTp t tp) = parens-unless (is-app p) (term-to-stringh (AppTp t tp) t ^ " · " ^ type-to-string tp )
term-to-stringh p (Hole _) = "●"
term-to-stringh p (Lam pi l pi' x o t) = 
  parens-unless (is-abs p) (lam-to-string l ^ " " ^ x ^ optClass-to-string o ^ " . " ^ term-to-stringh (Lam pi l pi' x o t) t)
term-to-stringh p (Parens _ t _) = term-to-string t
term-to-stringh p (Var _ x) = x
term-to-stringh p (Beta _) = "β"
term-to-stringh p (Delta _ t) = "(δ" ^ " " ^ term-to-string t ^ ")"
term-to-stringh p (PiInj _ n t) = "(π" ^ n ^ " " ^ term-to-string t ^ ")"
term-to-stringh p (Epsilon _ lr m t) = "(ε" ^ leftRight-to-string lr ^ maybeMinus-to-string m ^ " " ^ term-to-string t ^ ")"
term-to-stringh p (Sigma _ t) = "(ς " ^ term-to-string t ^ ")"
term-to-stringh p (Theta _ u t ts) = "(" ^ theta-to-string u ^ " " ^ term-to-string t ^ lterms-to-stringh ts ^ ")"
term-to-stringh p (Rho _ t t') = "(ρ " ^ term-to-string t ^ " - " ^ term-to-string t' ^ ")"
term-to-stringh p (Chi _ T t') = "(χ " ^ maybeAtype-to-string T ^ " - " ^ term-to-string t' ^ ")"

type-to-stringh p (Abs pi b pi' x t t') = 
  parens-unless (is-abs p) (binder-to-string b ^ " " ^ x ^ " : " ^ tk-to-string t ^ " . " ^ type-to-stringh (Abs pi b pi' x t t') t')
type-to-stringh p (TpLambda pi pi' x tk t) = 
  parens-unless (is-abs p) ("λ " ^ x ^ " : " ^ tk-to-string tk ^ " . " ^ type-to-stringh (TpLambda pi pi' x tk t) t )
type-to-stringh p (Iota pi x m t) = parens-unless (is-abs p) ("ι " ^ x ^ optClass-to-string m ^ " . " 
                                  ^ type-to-stringh (Iota pi x m t) t)
type-to-stringh p (Lft _ _ X x x₁) = "(↑ " ^ X ^ " . " ^ term-to-string x ^ " : " ^ liftingType-to-string x₁ ^ ")"
type-to-stringh p (TpApp t t₁) = parens-unless (is-app p) (type-to-stringh (TpApp t t₁) t ^ " · " ^ type-to-string t₁)
type-to-stringh p (TpAppt t t') = parens-unless (is-app p) (type-to-stringh (TpAppt t t') t ^ " " ^ term-to-string t')
type-to-stringh p (TpArrow x t) = parens-unless (is-arrow p) (type-to-string x ^ " → " ^  type-to-stringh (TpArrow x t) t)
type-to-stringh p (TpEq t1 t2) = "(" ^ term-to-string t1 ^ " ≃ " ^ term-to-string t2 ^ ")"
type-to-stringh p (TpParens _ t _) = type-to-string t
type-to-stringh p (TpVar _ x) = x
type-to-stringh p (NoSpans t _) = type-to-string t

kind-to-stringh p (KndArrow k k') =
  parens-unless (is-arrow p) (kind-to-string k ^ " → " ^ kind-to-stringh (KndArrow k k') k')
kind-to-stringh p (KndParens _ k _) = kind-to-string k
kind-to-stringh p (KndPi pi pi' x u k) = 
  parens-unless (is-abs p) ("Π " ^ x ^ " : " ^ tk-to-string u ^ " . " ^ kind-to-stringh (KndPi pi pi' x u k) k )
kind-to-stringh p (KndTpArrow x k) = parens-unless (is-arrow p) (type-to-string x ^ " → " ^ kind-to-stringh (KndTpArrow x k) k)
kind-to-stringh p (KndVar _ x) = x
kind-to-stringh p (Star _) = "★"

optClass-to-string NoClass = ""
optClass-to-string (SomeClass x) = " : " ^ tk-to-string x

tk-to-string (Tkk k) = kind-to-string k
tk-to-string (Tkt t) = type-to-string t

liftingType-to-stringh p (LiftArrow t t₁) = 
  parens-unless (is-arrow p) (liftingType-to-string t ^ " → " ^ liftingType-to-stringh (LiftArrow t t₁) t₁ )
liftingType-to-stringh p (LiftTpArrow t t₁) = 
  parens-unless (is-arrow p) (type-to-string t ^ " → " ^ liftingType-to-stringh (LiftTpArrow t t₁) t₁ )
liftingType-to-stringh p (LiftParens _ t _) = liftingType-to-string t
liftingType-to-stringh p (LiftPi pi x x₁ t) = 
  parens-unless (is-abs p) ("Π " ^ x ^ " : " ^ type-to-string x₁ ^ " . " ^ liftingType-to-stringh (LiftPi pi x x₁ t) t)
liftingType-to-stringh p (LiftStar _) = "☆"

lterms-to-stringh (LtermsNil _) = ""
lterms-to-stringh (LtermsCons t ts) = " " ^ term-to-string t ^ lterms-to-stringh ts

maybeAtype-to-string NoAtype = ""
maybeAtype-to-string (Atype T) = type-to-string T

to-string : {ed : exprd} → ⟦ ed ⟧ → string
to-string{TERM} = term-to-string
to-string{TYPE} = type-to-string
to-string{KIND} = kind-to-string
to-string{LIFTINGTYPE} = liftingType-to-string

to-string-if : {ed : exprd} → maybe (⟦ ed ⟧) → string
to-string-if (just e) = to-string e
to-string-if nothing = "[nothing]"
