module pretty where
open import general-util

-- Adapted from A Prettier Printer (Philip Wadler)
-- https://homepages.inf.ed.ac.uk/wadler/papers/prettier/prettier.pdf

-- The pretty printer
infixr 5 _:<|>_
infixr 6 _:<>_
infixr 6 _<>_

data DOC : Set where
  NIL : DOC
  _:<>_ : DOC → DOC → DOC
  NEST : ℕ → DOC → DOC
  TEXT : rope → DOC
  LINE : DOC
  _:<|>_ : DOC → DOC → DOC

data Doc : Set where
  Nil : Doc
  _Text_ : rope → Doc → Doc
  _Line_ : ℕ → Doc → Doc


nil = NIL
_<>_ = _:<>_
nest = NEST
text = TEXT
line = LINE

flatten : DOC → DOC
flatten NIL = NIL
flatten (x :<> y) = flatten x :<> flatten y
flatten (NEST i x) = NEST i (flatten x)
flatten (TEXT s) = TEXT s
flatten LINE = TEXT [[ " " ]]
flatten (x :<|> y) = flatten x

flatten-out : DOC → rope
flatten-out NIL = [[]]
flatten-out (x :<> y) = flatten-out x ⊹⊹ flatten-out y
flatten-out (NEST i x) = flatten-out x
flatten-out (TEXT s) = s
flatten-out LINE = [[ " " ]]
flatten-out (x :<|> y) = flatten-out x

group = λ x → flatten x :<|> x


fold : ∀ {ℓ} {X : Set ℓ} → ℕ → X → (X → X) → X
fold 0 z s = z
fold (suc n) z s = s (fold n z s)

copy : ∀ {ℓ} {X : Set ℓ} → ℕ → X → 𝕃 X
copy i x = fold i [] (x ::_)

layout : Doc → rope
layout Nil = [[]]
layout (s Text x) = s ⊹⊹ layout x
layout (i Line x) = [[ 𝕃char-to-string ('\n' :: copy i ' ') ]] ⊹⊹ layout x

_∸'_ : ℕ → ℕ → maybe ℕ
m ∸' n with suc m ∸ n
...| zero = nothing
...| suc o = just o

fits : maybe ℕ → Doc → 𝔹
fits nothing x  = ff
fits (just w) Nil = tt
fits (just w) (s Text x) = fits (w ∸' rope-length s) x
fits (just w) (i Line x) = tt



{-# TERMINATING #-}
be : ℕ → ℕ → 𝕃 (ℕ × DOC) → Doc
better : ℕ → ℕ → Doc → Doc → Doc
best : ℕ → ℕ → DOC → Doc

better w k x y = if fits (w ∸' k) x then x else y
best w k x = be w k [ 0 , x ]

be w k [] = Nil
be w k ((i , NIL) :: z) = be w k z
be w k ((i , x :<> y) :: z) = be w k ((i , x) :: (i , y) :: z)
be w k ((i , NEST j x) :: z) = be w k ((i + j , x) :: z)
be w k ((i , TEXT s) :: z) = s Text be w (k + rope-length s) z
be w k ((i , LINE) :: z) = i Line be w i z
be w k ((i , x :<|> y) :: z) = better w k (be w k ((i , x) :: z)) (be w k ((i , y) :: z))


pretty : ℕ → DOC → rope
pretty w x = layout (best w 0 x)



-- Utility functions

infixr 6 _<+>_ _</>_ _<+/>_
_<+>_ : DOC → DOC → DOC
x <+> y = x <> text [[ " " ]] <> y
_</>_ : DOC → DOC → DOC
x </> y = x <> line <> y

folddoc : (DOC → DOC → DOC) → 𝕃 DOC → DOC
folddoc f [] = nil
folddoc f (x :: []) = x
folddoc f (x :: xs) = f x (folddoc f xs)

spread = folddoc _<+>_

stack = folddoc _</>_

bracket : string → DOC → string → DOC
bracket l x r = group (text [[ l ]] <> nest 2 (line <> x) <> line <> text [[ r ]])

_<+/>_ : DOC → DOC → DOC
x <+/> y = x <> (text [[ " " ]] :<|> line) <> y

{-# TERMINATING #-}
fill : 𝕃 DOC → DOC
fill [] = nil
fill (x :: []) = x
fill (x :: y :: zs) = (flatten x <+> fill (flatten y :: zs)) :<|> (x </> fill (y :: zs))


{-# TERMINATING #-}
filln : 𝕃 (ℕ × DOC) → DOC
filln [] = nil
filln ((i , x) :: []) = nest i x
filln ((i , x) :: (j , y) :: zs) =
  (flatten x <+> filln ((j , flatten y) :: zs))
    :<|> (nest i x <> nest j line <> filln ((j , y) :: zs))

{-# TERMINATING #-}
fill-last : ℕ → 𝕃 DOC → DOC
fill-last i [] = nil
fill-last i (x :: []) = nest i x
fill-last i (x :: y :: []) = (flatten x <+> flatten y) :<|> (nest i (x </> y))
fill-last i (x :: y :: zs) = (flatten x <+> fill-last i (flatten y :: zs)) :<|> (x </> fill-last i (y :: zs))
