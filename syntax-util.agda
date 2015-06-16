module syntax-util where

open import lib
open import cedille-types

toplevel-drop-type-parens : type → type
toplevel-drop-type-parens (Ltype (TpParens x)) = toplevel-drop-type-parens x
toplevel-drop-type-parens (Ltype x) = (Ltype x)
toplevel-drop-type-parens x = x

kind-to-string : kind → string
tk-to-string : tk → string
type-to-string : type → string
ltype-to-string : ltype → string
term-to-string : term → string
lterm-to-string : lterm → string
ip-to-string : ip → string
al-to-string : al → string
ctorset-to-string : ctorset → string
liftingType-to-string : liftingType → string

kind-to-string (KndArrow k k') = "(" ^ kind-to-string k ^ " → " ^ kind-to-string k' ^ ")"
kind-to-string (KndParens k) = kind-to-string k
kind-to-string (KndPi x u k) = "(Π " ^ x ^ " : " ^ tk-to-string u ^ " . " ^ kind-to-string k ^ ")"
kind-to-string (KndTpArrow x k) = "(" ^ ltype-to-string x ^ " → " ^ kind-to-string k ^ ")"
kind-to-string (KndVar x) = x
kind-to-string Star = "★"

tk-to-string (Tkk k) = kind-to-string k
tk-to-string (Tkt t) = type-to-string t

type-to-string (AbsTp1 b x t1 t2) = "(" ^ (ip-to-string b) ^ " " ^ x ^ " : " ^ type-to-string t1 ^ " . " ^ type-to-string t2 ^ ")"
type-to-string (AbsTp2 b x t1 t2) = "(" ^ (al-to-string b) ^ " " ^ x ^ " : " ^ tk-to-string t1 ^ " . " ^ type-to-string t2 ^ ")"
type-to-string (Ltype x) = ltype-to-string x
type-to-string (Nu x k θ t) = "(ν" ^ " " ^ x ^ " : " ^ kind-to-string k ^ " | " ^ ctorset-to-string θ ^ " . " ^ type-to-string t ^ ")"
type-to-string (TpArrow x t) = "(" ^ ltype-to-string x ^ " → " ^  type-to-string t ^ ")"

ip-to-string Iota = "ι"
ip-to-string Pi = "Π"

al-to-string All = "∀"
al-to-string Lambda = "λ"

ltype-to-string (Lft x) = "↑ " ^ (liftingType-to-string x) ^ " -"
ltype-to-string (TpApp t t₁) = "(" ^ ltype-to-string t ^ " " ^ ltype-to-string t₁ ^ ")"
ltype-to-string (TpAppt t x) = "(" ^ ltype-to-string t ^ " " ^ lterm-to-string x ^ ")"
ltype-to-string (TpParens x) = type-to-string x
ltype-to-string (TpVar x) = x
ltype-to-string U = "𝓤"

term-to-string (App t t₁) = "(" ^ term-to-string t ^ " " ^ term-to-string t₁ ^ ")"
term-to-string (Lterm x) = lterm-to-string x
term-to-string (Var x) = x

ctorset-to-string (Add x x₁ θ) = term-to-string x ^ " ∈ " ^ type-to-string x₁ ^ " , " ^ ctorset-to-string θ
ctorset-to-string Empty = "·"

liftingType-to-string (LiftArrow t t₁) = "(" ^ liftingType-to-string t ^ " → " ^ liftingType-to-string t₁ ^ ")"
liftingType-to-string (LiftParens t) = liftingType-to-string t
liftingType-to-string (LiftPi x x₁ t) = "(π " ^ x ^ " : " ^ type-to-string x₁ ^ " . " ^ liftingType-to-string t ^ ")"
liftingType-to-string LiftStar = "☆"

lterm-to-string (Lam x x₁) = "(λ " ^ x ^ " . " ^ term-to-string x₁ ^ ")"
lterm-to-string (Paren x) = term-to-string x