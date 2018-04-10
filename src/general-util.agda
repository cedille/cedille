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

maybe-join : ∀ {a} {A : Set a} → maybe (maybe A) → maybe A
maybe-join = maybe-else nothing id

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

-- functions.agda
curry : ∀{ℓ₁ ℓ₂ ℓ₃}{A : Set ℓ₁}{B : Set ℓ₂}{C : Set ℓ₃}
        → (A × B → C) → A → B → C
curry f a b = f (a , b)

uncurry : ∀{ℓ₁ ℓ₂ ℓ₃}{A : Set ℓ₁}{B : Set ℓ₂}{C : Set ℓ₃}
          → (f : A → B → C) → (p : A × B) → C
uncurry f (a , b) = f a b

infix 0 case_return_of_ case_of_

case_return_of_ :
  ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁}
  (x : A) (B : A → Set ℓ₂) → ((x : A) → B x) → B x
case x return B of f = f x

case_of_ : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
case x of f = case_return_of_ x _ f

flip : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
       → (A → B → C) → (B → A → C)
flip f = λ b a → f a b

-- list.agda

take : ∀{ℓ}{A : Set ℓ} → ℕ → 𝕃 A → 𝕃 A
take 0 l = []
take (suc n) (x :: l) = x :: (take n l)
take (suc n) [] = []

drop : ∀{ℓ}{A : Set ℓ} → ℕ → 𝕃 A → 𝕃 A
drop zero xs = xs
drop (suc _) [] = []
drop (suc n) (x :: xs) = drop n xs

zip-with : ∀{ℓ₁ ℓ₂ ℓ₃}{A : Set ℓ₁}{B : Set ℓ₂}{C : Set ℓ₃}
           → (A → B → C) → 𝕃 A → 𝕃 B → 𝕃 C
zip-with f xs ys = map (uncurry f) (zip xs ys)

for_yield_ : ∀ {a b} {A : Set a} {B : Set b} → 𝕃 A → (A → B) → 𝕃 B
for xs yield f = map f xs

for_accum_do_ : ∀ {a b} {A : Set a} {B : Set b} → 𝕃 A → B → (A → B → B) → B
for xs accum n do f = foldr f n xs

-- error.agda
err-guard : 𝔹 → string → error-t ⊤
err-guard tt msg = yes-error msg
err-guard ff _   = no-error triv

-- Some file writing functions
data IOMode : Set where
  ReadMode : IOMode
  WriteMode : IOMode
  AppendMode : IOMode
  ReadWriteMode : IOMode

postulate
  Handle : Set
  -- IOMode : Set
  openFile : string → IOMode -> IO Handle
  closeFile : Handle -> IO ⊤
  hPutStr : Handle → string → IO ⊤
  hSetToLineBuffering : Handle → IO ⊤
  hFlush : Handle → IO ⊤
  stdout : Handle

{-# COMPILED_TYPE Handle System.IO.Handle #-}
{-# COMPILED_DATA IOMode System.IO.IOMode System.IO.ReadMode System.IO.WriteMode System.IO.AppendMode System.IO.ReadWriteMode #-}
{-# COMPILED hSetToLineBuffering (\hdl -> System.IO.hSetBuffering hdl System.IO.LineBuffering) #-}
{-# COMPILED hFlush System.IO.hFlush #-}
{-# COMPILED stdout System.IO.stdout #-}
{-# COMPILED openFile (\fp -> (\mode -> do outh <- System.IO.openFile (Data.Text.unpack fp) mode; System.IO.hSetNewlineMode outh System.IO.noNewlineTranslation; System.IO.hSetEncoding outh System.IO.utf8; return outh)) #-}
{-# COMPILED closeFile System.IO.hClose #-}
{-# COMPILED hPutStr (\ hdl -> (\ s -> Data.Text.IO.hPutStr hdl s)) #-}

clearFile : string → IO ⊤
clearFile fp = openFile fp WriteMode >>= λ hdl → hPutStr hdl "" >> closeFile hdl

flush : IO ⊤
flush = hFlush stdout

setToLineBuffering : IO ⊤
setToLineBuffering = hSetToLineBuffering stdout

infixl 1 _>>≠_

_>>≠_  : ∀{A B : Set} → IO A → IO B → IO A
(io₁ >>≠ io₂) = io₁ >>= λ result → io₂ >> return result

withFile : {A : Set} → string → IOMode → (Handle → IO A) → IO A
withFile fp mode f = openFile fp mode >>= λ hdl → f hdl >>≠ closeFile hdl

-- Coordinated Universal Time
infix 15 _utc-after_ _utc-before_

postulate
  UTC : Set
  getCurrentTime : IO UTC
  _utc-after_ : UTC → UTC → 𝔹
  _utc-before_ : UTC → UTC → 𝔹
  utcToString : UTC → string
  getModificationTime : string → IO UTC

{-# IMPORT Data.Time.Clock #-}
{-# IMPORT Data.Time.Calendar #-}
{-# COMPILED_TYPE UTC Data.Time.Clock.UTCTime #-}
{-# COMPILED getCurrentTime Data.Time.Clock.getCurrentTime #-}
{-# COMPILED _utc-after_ (>) #-}
{-# COMPILED _utc-before_ (<) #-}
{-# COMPILED utcToString (\ t -> Data.Text.pack (show t)) #-}
{-# COMPILED getModificationTime (\ s -> System.Directory.getModificationTime (Data.Text.unpack s)) #-}

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

writeRopeToFile : (filepath : string) → rope → IO ⊤
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

instance
  IO-monad : monad IO
  IO-monad = record { returnM = return ; bindM = _>>=_ }

Id : Set → Set
Id A = A

instance
  Id-monad : monad Id
  Id-monad = record {returnM = λ a → a ; bindM = λ a f → f a }
