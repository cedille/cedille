module general-util where

open import lib
open import functions public

get-file-contents : (filename : string) → IO (maybe string)
get-file-contents e = 
  doesFileExist e >>= λ b → 
     if b then
      (readFiniteFile e >>= λ s → return (just s))
     else
      return nothing

maybe-else : ∀{ℓ}{A B : Set ℓ} → B → (A → B) → maybe A → B
maybe-else y f (just x) = f x
maybe-else y f nothing = y

maybe-else' : ∀{ℓ}{A B : Set ℓ} → maybe A → B → (A → B) → B
maybe-else' m y f = maybe-else y f m

maybe-join : ∀ {a} {A : Set a} → maybe (maybe A) → maybe A
maybe-join = maybe-else nothing id

maybe-equal? : ∀ {a} {A : Set a} → (A → A → 𝔹) → (m₁ m₂ : maybe A) → 𝔹
maybe-equal? f (just x) (just x₁) = f x x₁
maybe-equal? f (just x) nothing = ff
maybe-equal? f nothing (just x) = ff
maybe-equal? f nothing nothing = tt

_≫maybe_ : ∀ {ℓ}{A B : Set ℓ} → maybe A → maybe B → maybe B
nothing ≫maybe f = nothing
just x  ≫maybe f = f

_maybe-or_ : ∀ {ℓ} {A : Set ℓ} → maybe A → maybe A → maybe A
(nothing maybe-or ma) = ma
(just a  maybe-or ma) = just a

maybe-not : ∀ {ℓ} {A : Set ℓ} → maybe A → maybe ⊤
maybe-not (just a) = nothing
maybe-not nothing = just triv

maybe-if : 𝔹 → maybe ⊤
maybe-if tt = just triv
maybe-if ff = nothing

trie-lookupd : ∀ {A : Set} → trie A → string → A → A
trie-lookupd t s d with trie-lookup t s
trie-lookupd t s d | nothing = d
trie-lookupd t s d | just x = x

trie-lookup-else : ∀{A : Set} → A → trie A → string → A
trie-lookup-else d t s = trie-lookupd t s d

trie-single : ∀{A : Set} → string → A → trie A
trie-single s x = trie-insert empty-trie s x

trie-any : ∀{A : Set} → (A → 𝔹) → trie A  → 𝔹
trie-cal-any : ∀{A : Set} → (A → 𝔹) → cal (trie A)  → 𝔹
trie-any f (Node odata ts) = maybe-else (trie-cal-any f ts) f odata
trie-cal-any f [] = ff
trie-cal-any f ((c , t) :: cs) = trie-any f t || trie-cal-any f cs 

trie-all : ∀{A : Set} → (A → 𝔹) → trie A → 𝔹
trie-all f = ~_ ∘ trie-any (~_ ∘ f)

trie-lookup𝕃 : ∀ {A : Set} → trie (𝕃 A) → string → 𝕃 A
trie-lookup𝕃 t s = trie-lookupd t s []

trie-lookup𝕃2 : ∀ {A : Set} → trie (string × 𝕃 A) → string → string × 𝕃 A
trie-lookup𝕃2 t s = trie-lookupd t s ("[nomod]" , [])

trie-lookup-string : trie string → string → string
trie-lookup-string t s = trie-lookupd t s "[not-found]"

trie-insert-append : ∀ {A : Set} → trie (𝕃 A) → string → A → trie (𝕃 A)
trie-insert-append t s a = trie-insert t s (a :: (trie-lookup𝕃 t s))

trie-insert-append2 : ∀ {A : Set} → trie (string × 𝕃 A) → string → string → A → trie (string × 𝕃 A)
trie-insert-append2 t s mn a = trie-insert t s (mn , (a :: snd (trie-lookup𝕃2 t s)))

trie-fill : ∀{A : Set} → trie A → 𝕃 (string × A) → trie A
trie-fill t ((s , a) :: vs) = trie-fill (trie-insert t s a) vs
trie-fill t [] = t

trie-empty? : ∀ {A} → trie A → 𝔹
trie-empty? t = ~ trie-nonempty t

trie-filter : ∀ {A} → (A → 𝔹) → trie A → trie A
cal-filter  : ∀ {A} → (A → 𝔹) → cal (trie A) → cal (trie A)

trie-filter f (Node odata ts'@(c :: ts))
  = Node odata (cal-filter f ts')
trie-filter f t@(Node (just x) [])
  = if f x then t else empty-trie
trie-filter f (Node nothing [])
  = empty-trie

cal-filter f [] = []
cal-filter f ((a , t) :: c)
  with trie-filter f t | cal-filter f c
... | t' | c'
  = if trie-empty? t then c' else (a , t') :: c'

trie-catMaybe : ∀ {A} → trie (maybe A) → trie A
cal-catMaybe  : ∀ {A} → cal (trie (maybe A)) → cal (trie A)

trie-catMaybe (Node odata ts'@(t :: ts)) = Node (maybe-join odata) (cal-catMaybe ts')
trie-catMaybe (Node odata []) = maybe-else empty-trie (λ a → Node (just a) []) (maybe-join odata)

cal-catMaybe [] = []
cal-catMaybe ((c , tr) :: trs)
  with trie-catMaybe tr | cal-catMaybe trs
... | tr' | trs' = if trie-empty? tr' then trs' else (c , tr') :: trs'

trie-equal? : ∀ {A : Set} → (A → A → 𝔹) → (t₁ t₂ : trie A) → 𝔹
trie-equal? {A} f t₁ t₂ =
    length t₁𝕃 =ℕ length t₂𝕃
  && list-all check-elems t₁𝕃
  where
    t₁𝕃 = trie-mappings t₁
    t₂𝕃 = trie-mappings t₂

    check-elems : string × A → 𝔹
    check-elems (name , dat₁) with trie-lookup t₂ name
    ... | nothing = ff
    ... | just dat₂ = f dat₁ dat₂

string-split-h : 𝕃 char → char → 𝕃 char → 𝕃 string → 𝕃 string
string-split-h [] delim str-build out = reverse ((𝕃char-to-string (reverse str-build)) :: out)
string-split-h (c :: cs) delim str-build out with (c =char delim)
... | tt = string-split-h cs delim [] ((𝕃char-to-string (reverse str-build)) :: out)
... | ff = string-split-h cs delim (c :: str-build) out

string-split : string → char → 𝕃 string
string-split str delim = string-split-h (string-to-𝕃char str) delim [] []

undo-escape-string-h : 𝕃 char → 𝕃 char → 𝕃 char
undo-escape-string-h ('\\' :: 'n' :: rest) so-far = undo-escape-string-h rest ('\n' :: so-far)
undo-escape-string-h ('\\' :: '\"' :: rest) so-far = undo-escape-string-h rest ('\"' :: so-far)
undo-escape-string-h (c :: rest) so-far = undo-escape-string-h rest (c :: so-far)
undo-escape-string-h [] so-far = reverse so-far

undo-escape-string : string → string
undo-escape-string str = 𝕃char-to-string (undo-escape-string-h (string-to-𝕃char str) [])

is-pfx : (pfx str : string) → maybe string
is-pfx pfx str = h (string-to-𝕃char pfx) (string-to-𝕃char str) where
  h : 𝕃 char → 𝕃 char → maybe string
  h [] cs = just (𝕃char-to-string cs)
  h (cₚ :: csₚ) [] = nothing
  h (cₚ :: csₚ) (cₛ :: csₛ) with cₚ =char cₛ
  ...| ff = nothing
  ...| tt = h csₚ csₛ

-- functions.agda
curry : ∀{ℓ₁ ℓ₂ ℓ₃}{A : Set ℓ₁}{B : Set ℓ₂}{C : Set ℓ₃}
        → (A × B → C) → A → B → C
curry f a b = f (a , b)

uncurry : ∀{ℓ₁ ℓ₂ ℓ₃}{A : Set ℓ₁}{B : Set ℓ₂}{C : Set ℓ₃}
          → (f : A → B → C) → (p : A × B) → C
uncurry f (a , b) = f a b

uncurry₂ : ∀{a b c d}{A : Set a}{B : Set b}{C : Set c}{D : Set d}
          → (f : A → B → C → D) → (p : A × B × C) → D
uncurry₂ f (a , b , c) = f a b c

elim-pair : ∀{ℓ₁ ℓ₂ ℓ₃}{A : Set ℓ₁}{B : Set ℓ₂}{C : Set ℓ₃}
            → A × B → (A → B → C) → C
elim-pair (a , b) f = f a b

elim-Σi : ∀ {ℓ ℓ' ℓ''} {A : Set ℓ} {B : A → Set ℓ'} {X : Set ℓ''}
          → Σi A B → ({a : A} → B a → X) → X
elim-Σi (, b) f = f b

infixr 0 case_return_of_ case_of_

case_return_of_ :
  ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁}
  (x : A) (B : A → Set ℓ₂) → ((x : A) → B x) → B x
case x return B of f = f x

case_of_ : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
case x of f = case_return_of_ x _ f

case₂_,_of_ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} → A → B → (A → B → C) → C
case₂ x , y of f = f x y

flip : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
       → (A → B → C) → (B → A → C)
flip f = λ b a → f a b

const : ∀ {a b} {A : Set a} {B : Set b} →
        A → B → A
const a b = a

infixr 0 _$_
_$_ : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → A → B
f $ x = f x

-- _∘_ just needs a fixity and association declaration in the IAL
infixr 9 _∘'_
_∘'_ : ∀ {a b c} {A : Set a}{B : Set b}{C : Set c}
         → (B → C) → (A → B) → A → C
g ∘' f = λ a → g (f a)

-- list.agda

take : ∀{ℓ}{A : Set ℓ} → ℕ → 𝕃 A → 𝕃 A
take 0 l = []
take (suc n) (x :: l) = x :: (take n l)
take (suc n) [] = []

drop : ∀{ℓ}{A : Set ℓ} → ℕ → 𝕃 A → 𝕃 A
drop zero xs = xs
drop (suc _) [] = []
drop (suc n) (x :: xs) = drop n xs

drop-last : ∀{ℓ}{A : Set ℓ} → ℕ → 𝕃 A → 𝕃 A
drop-last n xs = take (length xs ∸ n) xs

zip-with : ∀{ℓ₁ ℓ₂ ℓ₃}{A : Set ℓ₁}{B : Set ℓ₂}{C : Set ℓ₃}
           → (A → B → C) → 𝕃 A → 𝕃 B → 𝕃 C
zip-with f xs ys = map (uncurry f) (zip xs ys)

for_yield_ : ∀ {a b} {A : Set a} {B : Set b} → 𝕃 A → (A → B) → 𝕃 B
for xs yield f = map f xs

for_accum_use_ : ∀ {a b} {A : Set a} {B : Set b} → 𝕃 A → B → (A → B → B) → B
for xs accum n use f = foldr f n xs


foldl : ∀{ℓ ℓ'}{A : Set ℓ}{B : Set ℓ'} → (A → B → B) → B → 𝕃 A → B
foldl f b [] = b
foldl f b (a :: as) = foldl f (f a b) as

foldr' : ∀{ℓ ℓ'}{A : Set ℓ}{B : Set ℓ'} → B → (A → B → B) → 𝕃 A → B
foldr' = flip foldr

-- error.agda
err-guard : 𝔹 → string → error-t ⊤
err-guard tt msg = yes-error msg
err-guard ff _   = no-error triv

-- sum.agda
either-else' : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} → A ∨ B → (A → C) → (B → C) → C
either-else' (inj₁ x) f g = f x
either-else' (inj₂ y) f g = g y

err⊎-guard : ∀ {e} {E : Set e} → 𝔹 → E → E ∨ ⊤
err⊎-guard tt err = inj₁ err
err⊎-guard ff _   = inj₂ triv

infixl 1 _≫⊎_
_≫⊎_ : ∀ {E B : Set} → E ∨ ⊤ → E ∨ B → E ∨ B
m₁ ≫⊎ m₂ = m₁ ≫=⊎ λ _ → m₂

-- Some file writing functions
data IOMode : Set where
  ReadMode : IOMode
  WriteMode : IOMode
  AppendMode : IOMode
  ReadWriteMode : IOMode

filepath = string

postulate
  Handle : Set
  -- IOMode : Set
  openFile : filepath → IOMode -> IO Handle
  closeFile : Handle -> IO ⊤
  hPutStr : Handle → string → IO ⊤
  hSetToLineBuffering : Handle → IO ⊤
  hFlush : Handle → IO ⊤
  stdout : Handle
  doesDirectoryExist : filepath → IO 𝔹

{-# FOREIGN GHC import qualified System.IO #-}
{-# FOREIGN GHC import qualified Data.Text.IO #-}
{-# FOREIGN GHC import qualified System.Directory #-}
{-# COMPILE GHC Handle = type System.IO.Handle #-}
{-# COMPILE GHC IOMode = data System.IO.IOMode (System.IO.ReadMode | System.IO.WriteMode | System.IO.AppendMode | System.IO.ReadWriteMode) #-}
{-# COMPILE GHC hSetToLineBuffering = \ hdl -> System.IO.hSetBuffering hdl System.IO.LineBuffering #-}
{-# COMPILE GHC hFlush = System.IO.hFlush #-}
{-# COMPILE GHC stdout = System.IO.stdout #-}
{-# COMPILE GHC openFile = \ fp mode -> do outh <- System.IO.openFile (Data.Text.unpack fp) mode; System.IO.hSetNewlineMode outh System.IO.noNewlineTranslation; System.IO.hSetEncoding outh System.IO.utf8; return outh #-}
{-# COMPILE GHC closeFile = System.IO.hClose #-}
{-# COMPILE GHC hPutStr = Data.Text.IO.hPutStr #-}
{-# COMPILE GHC doesDirectoryExist = System.Directory.doesDirectoryExist . Data.Text.unpack #-}

clearFile : filepath → IO ⊤
clearFile fp = openFile fp WriteMode >>= λ hdl → hPutStr hdl "" >> closeFile hdl

flush : IO ⊤
flush = hFlush stdout

setToLineBuffering : IO ⊤
setToLineBuffering = hSetToLineBuffering stdout

infixl 1 _>>≠_ _>≯_ _>>=r_ _>>r_ _>>∘_

_>>≠_  : ∀{A B : Set} → IO A → (A → IO B) → IO A
(io₁ >>≠ io₂) = io₁ >>= λ result → io₂ result >> return result

_>≯_ : ∀{A B : Set} → IO A → IO B → IO A
(io₁ >≯ io₂) = io₁ >>= λ result → io₂ >> return result

_>>=r_ : ∀{A B : Set} → IO A → (A → B) → IO B
a >>=r f = a >>= (return ∘ f)

_>>r_ : ∀{A B : Set} → IO A → B → IO B
a >>r b = a >> return b

_>>∘_ : ∀{A B : Set} → IO A → IO (A → IO B) → IO B
a >>∘ f = a >>= λ a → f >>= λ f → f a

withFile : {A : Set} → filepath → IOMode → (Handle → IO A) → IO A
withFile fp mode f = openFile fp mode >>= λ hdl → f hdl >≯ closeFile hdl

-- Coordinated Universal Time
infix 15 _utc-after_ _utc-before_

postulate
  UTC : Set
  getCurrentTime : IO UTC
  _utc-after_ : UTC → UTC → 𝔹
  _utc-before_ : UTC → UTC → 𝔹
  utcToString : UTC → string
  getModificationTime : filepath → IO UTC
  getCurrentDirectory : IO filepath
  pathSeparator : char

{-# FOREIGN GHC import qualified Data.Time.Clock #-}
{-# FOREIGN GHC import qualified Data.Time.Calendar #-}
{-# FOREIGN GHC import qualified System.FilePath #-}
{-# COMPILE GHC UTC = type Data.Time.Clock.UTCTime #-}
{-# COMPILE GHC getCurrentTime = Data.Time.Clock.getCurrentTime #-}
{-# COMPILE GHC _utc-after_ = (>) #-}
{-# COMPILE GHC _utc-before_ = (<) #-}
{-# COMPILE GHC utcToString = Data.Text.pack . show #-}
{-# COMPILE GHC getModificationTime = System.Directory.getModificationTime . Data.Text.unpack #-}
{-# COMPILE GHC getCurrentDirectory = System.Directory.getCurrentDirectory >>= return . Data.Text.pack #-}
{-# COMPILE GHC pathSeparator = System.FilePath.pathSeparator #-}

pathSeparatorString = 𝕃char-to-string [ pathSeparator ]

splitPath : filepath → 𝕃 string
splitPath = h [] [] ∘ string-to-𝕃char where
  cons-if-nonempty : 𝕃 char → 𝕃 string → 𝕃 string
  cons-if-nonempty [] acc = acc
  cons-if-nonempty cur acc = 𝕃char-to-string (reverse cur) :: acc
  h : 𝕃 string → 𝕃 char → 𝕃 char → 𝕃 string
  h acc cur [] = reverse (cons-if-nonempty cur acc)
  h acc cur (c :: cs) with c =char pathSeparator
  ...| tt = h (cons-if-nonempty cur acc) [] cs
  ...| ff = h acc (c :: cur) cs

joinPath : 𝕃 string → filepath
joinPath [] = ""
joinPath (x :: []) = x
joinPath (x :: xs) = x ^ pathSeparatorString ^ joinPath xs

pathIsAbsolute : filepath → 𝔹
pathIsAbsolute = maybe-else ff (λ c → (c =char '~') || (c =char pathSeparator)) ∘ (head2 ∘ string-to-𝕃char)

-- string binary tree, for more efficient I/O printing than concatenation
data rope : Set where
  _⊹⊹_ : rope → rope → rope
  [[_]] : string → rope

infixl 9 _⊹⊹_
infix 9 [[_]]

[[]] : rope
[[]] = [[ "" ]]

rope-to-string : rope → string
rope-to-string = flip h "" where
  h : rope → string → string
  h (s₁ ⊹⊹ s₂) = h s₁ ∘ h s₂
  h [[ s ]] acc = s ^ acc

putStrLn : string → IO ⊤
putStrLn str = putStr str >> putStr "\n" -- >> flush

putRope : rope → IO ⊤
-- putRope = putStr ∘ rope-to-string
putRope s = h s (return triv) where
  h : rope → IO ⊤ → IO ⊤
  h (s₁ ⊹⊹ s₂) io = h s₁ (h s₂ io)
  h [[ s ]] io = putStr s >> io

putRopeLn : rope → IO ⊤
putRopeLn s = putRope s >> putStr "\n" -- >> flush

hPutRope : Handle → rope → IO ⊤
hPutRope outh s = h s (return triv) outh where
  h : rope → IO ⊤ → Handle → IO ⊤
  h (s₁ ⊹⊹ s₂) io outh = h s₁ (h s₂ io outh) outh
  h [[ s ]] io outh = hPutStr outh s >> io

writeRopeToFile : filepath → rope → IO ⊤
writeRopeToFile fp s = clearFile fp >> openFile fp AppendMode >>= λ hdl → hPutRope hdl s >> closeFile hdl

stringset-singleton : string → stringset
stringset-singleton x = stringset-insert empty-stringset x


record monad (F : Set → Set) : Set₁ where
  field
    returnM : ∀{A : Set} → A → F A
    bindM : ∀{A B : Set} → F A → (A → F B) → F B

returnM : ∀{F : Set → Set}{{m : monad F}}{A : Set} → A → F A
returnM {{m}} = monad.returnM m

infixl 1 _≫monad_ _≫=monad_
bindM : ∀{F : Set → Set}{{m : monad F}}{A B : Set} → F A → (A → F B) → F B
bindM {{m}} = monad.bindM m

_≫=monad_ : ∀{F : Set → Set}{{m : monad F}}{A B : Set} → F A → (A → F B) → F B
_≫=monad_ = bindM

bindM' : ∀{F : Set → Set}{{m : monad F}}{A B : Set} → F A → F B → F B
bindM' a b = bindM a (λ a → b)

_≫monad_ : ∀{F : Set → Set}{{m : monad F}}{A B : Set} → F A → F B → F B
_≫monad_ = bindM'

map-fst : ∀ {ℓ₀ ℓ₁ ℓ₂} {X₀ : Set ℓ₀} {X₁ : Set ℓ₁} {X₂ : Set ℓ₂} → (X₀ → X₂) → (X₀ × X₁) → (X₂ × X₁)
map-fst f (x₀ , x₁) = (f x₀ , x₁)

map-snd : ∀ {ℓ₀ ℓ₁ ℓ₂} {X₀ : Set ℓ₀} {X₁ : Set ℓ₁} {X₂ : Set ℓ₂} → (X₁ → X₂) → (X₀ × X₁) → (X₀ × X₂)
map-snd f (x₀ , x₁) = (x₀ , f x₁)

