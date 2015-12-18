module to-string where

open import lib
open import cedille-types

binder-to-string : binder → string
binder-to-string All = "∀"
binder-to-string Pi = "Π"
binder-to-string TpLambda = "λ"

maybeErased-to-string : maybeErased → string
maybeErased-to-string Erased = ""
maybeErased-to-string NotErased = "-"

lam-to-string : lam → string
lam-to-string ErasedLambda = "Λ"
lam-to-string KeptLambda = "λ"


type-to-string : type → string
term-to-string : term → string
kind-to-string : kind → string
optClass-to-string : optClass → string
tk-to-string : tk → string
liftingType-to-string : liftingType → string

type-to-string (Abs b x t t') = "(" ^ binder-to-string b ^ " " ^ x ^ " : " ^ tk-to-string t ^ " . " ^ type-to-string t' ^ ")"
type-to-string (Lft x x₁) = "↑" ^ term-to-string x ^ " : " ^ liftingType-to-string x₁
type-to-string (TpApp t t₁) = "(" ^ type-to-string t ^ " · " ^ type-to-string t₁ ^ ")"
type-to-string (TpAppt t t') = "(" ^ type-to-string t ^ " " ^ term-to-string t' ^ ")"
type-to-string (TpArrow x t) = "(" ^ type-to-string x ^ " → " ^  type-to-string t ^ ")"
type-to-string (TpEq t1 t2) = "(" ^ term-to-string t1 ^ " ≃ " ^ term-to-string t2 ^ ")"
type-to-string (TpParens t) = type-to-string t
type-to-string (TpVar x) = "x"

term-to-string (App t x t') = "(" ^ term-to-string t ^ (maybeErased-to-string x) ^ term-to-string t' ^ ")"
term-to-string Hole = "●"
term-to-string (Lam l x o t) = "(" ^ lam-to-string l ^ " " ^ optClass-to-string o ^ " . " ^ term-to-string t ^ ")"
term-to-string (Parens t) = term-to-string t
term-to-string (Var x) = x

kind-to-string (KndArrow k k') = "(" ^ kind-to-string k ^ " → " ^ kind-to-string k' ^ ")"
kind-to-string (KndParens k) = kind-to-string k
kind-to-string (KndPi x u k) = "(Π " ^ x ^ " : " ^ tk-to-string u ^ " . " ^ kind-to-string k ^ ")"
kind-to-string (KndTpArrow x k) = "(" ^ type-to-string x ^ " → " ^ kind-to-string k ^ ")"
kind-to-string (KndVar x) = x
kind-to-string Star = "★"

optClass-to-string NoClass = ""
optClass-to-string (SomeClass x) = " : " ^ tk-to-string x

tk-to-string (Tkk k) = kind-to-string k
tk-to-string (Tkt t) = type-to-string t

liftingType-to-string (LiftArrow t t₁) = "(" ^ liftingType-to-string t ^ " → " ^ liftingType-to-string t₁ ^ ")"
liftingType-to-string (LiftTpArrow t t₁) = "(" ^ type-to-string t ^ " → " ^ liftingType-to-string t₁ ^ ")"
liftingType-to-string (LiftParens t) = liftingType-to-string t
liftingType-to-string (LiftPi x x₁ t) = 
    "(Π " ^ x ^ " : " ^ type-to-string x₁ ^ " . " ^ liftingType-to-string t ^ ")"
liftingType-to-string LiftStar = "☆"
