module syntax-util where

open import lib
open import cedille-types

-- NB: \GTH is for Θ, while \Gth is for θ.  The characters are imperceptibly different at usual font size.

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
type-to-string (Lft x) = "↑ " ^ (liftingType-to-string x) ^ " -"
type-to-string (TpApp t t₁) = "(" ^ type-to-string t ^ " " ^ type-to-string t₁ ^ ")"
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
liftingType-to-string (LiftPi x x₁ t) = "(π " ^ x ^ " : " ^ type-to-string x₁ ^ " . " ^ liftingType-to-string t ^ ")"
liftingType-to-string LiftStar = "☆"


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