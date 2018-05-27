import cedille-options

module interactive-cmds (options : cedille-options.options) where

open import lib
open import functions
open import cedille-types
open import conversion
open import ctxt
open import general-util
open import spans options {Id}
open import syntax-util
open import to-string options
open import toplevel-state options {IO}
open import untyped-spans options {IO}
open import parser
open import rewriting
open import rename
open import classify options {Id}
import spans options {IO} as io-spans

{- Parsing -}

language-level-to-exprd : language-level → exprd
language-level-to-exprd ll-term = TERM
language-level-to-exprd ll-type = TYPE
language-level-to-exprd ll-kind = KIND

language-level-lift : language-level → Set
language-level-lift = ⟦_⟧ ∘ language-level-to-exprd
parsedExpr : language-level → Set
parsedExpr = maybe ∘ language-level-lift

ttk : string
ttk = "term, type, or kind"

expr : Set
expr = Σi language-level language-level-lift

either-to-expr : {pa : language-level} → Either string (language-level-lift pa) → parsedExpr pa
either-to-expr (Left e) = nothing
either-to-expr (Right e) = just e

var-is-type : ctxt → var → 𝔹
var-is-type Γ v = isJust (ctxt-lookup-type-var Γ v)

ll-disambiguate' : ctxt → term → expr
ll-disambiguate' Γ e @ (Var pi x) =
  if var-is-type Γ x then , TpVar pi x else , e
ll-disambiguate' Γ e @ (App t NotErased t') =
  case ll-disambiguate' Γ t of λ where
    (,_ {ll-type} T) → , TpAppt T t'
    _ → , e
ll-disambiguate' Γ e @ (AppTp t T') =
  case ll-disambiguate' Γ t of λ where
    (,_ {ll-type} T) → , TpApp T T'
    _ → , e
ll-disambiguate' Γ e @ (Lam pi KeptLambda pi' v (SomeClass atk) t ) =
  case ll-disambiguate' Γ t of λ where
    (,_ {ll-type} T) → , TpLambda pi pi' v atk T
    _ → , e
ll-disambiguate' Γ e @ (Parens pi t pi') =
  case ll-disambiguate' Γ t of λ where
    (,_ {ll-type} T) → , TpParens pi T pi'
    _ → , e
ll-disambiguate' Γ t = , t

ll-disambiguate : ctxt → expr → expr
ll-disambiguate Γ (,_ {ll-term} t) = ll-disambiguate' Γ t
ll-disambiguate Γ e = e

parse-string : (pa : language-level) → string → parsedExpr pa
parse-string pa = either-to-expr ∘ h pa where
  h : (pa : language-level) → string → Either string (language-level-lift pa)
  h ll-term = parseTerm
  h ll-type = parseType
  h ll-kind = parseKind

parse-err-msg : (failed-to-parse : string) → (as-a : string) → string
parse-err-msg failed-to-parse "" = "Failed to parse \\\\\"" ^ failed-to-parse ^ "\\\\\""
parse-err-msg failed-to-parse as-a = "Failed to parse \\\\\"" ^ failed-to-parse ^ "\\\\\" as a " ^ as-a

infixr 7 _≫nothing_ _-_!_≫parse_ _!_≫error_
_≫nothing_ : ∀{ℓ}{A : Set ℓ} → maybe A → maybe A → maybe A
(nothing ≫nothing m₂) = m₂
(m₁ ≫nothing m₂) = m₁

_-_!_≫parse_ : ∀{A B : Set} → (string → maybe A) → string → (error-msg : string) → (A → string ⊎ B) → string ⊎ B
(f - s ! e ≫parse f') = maybe-else (inj₁ (parse-err-msg s e)) f' (f s)

_!_≫error_ : ∀{E A B : Set} → maybe A → E → (A → E ⊎ B) → E ⊎ B
(just a ! e ≫error f) = f a
(nothing ! e ≫error f) = inj₁ e

map⊎ : ∀{E A B : Set} → E ⊎ A → (A → B) → E ⊎ B
map⊎ (inj₂ a) f = inj₂ (f a)
map⊎ (inj₁ e) f = inj₁ e

parse-try : ctxt → string → maybe expr
parse-try Γ s = maybe-map (ll-disambiguate Γ)
  (maybe-map ,_ (parse-string ll-term s) ≫nothing
   maybe-map ,_ (parse-string ll-type s) ≫nothing
   maybe-map ,_ (parse-string ll-kind s))

string-to-𝔹 : string → maybe 𝔹
string-to-𝔹 "tt" = just tt
string-to-𝔹 "ff" = just ff
string-to-𝔹 _ = nothing

string-to-language-level : string → maybe language-level
string-to-language-level "term" = just ll-term
string-to-language-level "type" = just ll-type
string-to-language-level "kind" = just ll-kind
string-to-language-level _ = nothing


{- Contextualization -}

record lci : Set where
  constructor mk-lci
  field
    ll : string
    x : var
    t : string
    T : string
    fn : string
    pi : posinfo

strings-to-lcis : 𝕃 string → 𝕃 lci
strings-to-lcis ss = strings-to-lcis-h ss [] where
  strings-to-lcis-h : 𝕃 string → 𝕃 lci → 𝕃 lci
  strings-to-lcis-h (ll :: x :: t :: T :: fn :: pi :: tl) items =
    strings-to-lcis-h tl (mk-lci ll x t T fn pi :: items)
  strings-to-lcis-h _ items = items

language-level-type-of : language-level → language-level
language-level-type-of ll-term = ll-type
language-level-type-of _ = ll-kind

merge-lci-ctxt : lci → ctxt → ctxt
merge-lci-ctxt (mk-lci nt v t T fn pi) Γ =
  maybe-else Γ (λ Γ → Γ) (string-to-language-level nt ≫=maybe λ nt →
    parse-string (language-level-type-of nt ) T ≫=maybe (h (parse-string nt t) ∘ ,_)) where
  h : {pa : language-level} → parsedExpr pa → expr → maybe ctxt
  h {ll-term} (just t) (,_ {ll-type} T) =
    just (ctxt-term-def pi localScope nonParamVar v t (qualif-type Γ T) Γ)
  h {ll-type} (just T) (,_ {ll-kind} k) =
    just (ctxt-type-def pi localScope nonParamVar v T (qualif-kind Γ k) Γ)
  h nothing (,_ {ll-type} T) = just (ctxt-term-decl pi localScope v T Γ)
  h nothing (,_ {ll-kind} k) = just (ctxt-type-decl pi localScope v k Γ)
  h _ _ = nothing

sort-lcis : 𝕃 lci → 𝕃 lci
sort-lcis = list-merge-sort.merge-sort lci λ l l' →
    posinfo-to-ℕ (lci.pi l) > posinfo-to-ℕ (lci.pi l')
  where import list-merge-sort

merge-lcis-ctxt : ctxt → 𝕃 string → ctxt
merge-lcis-ctxt c = foldr merge-lci-ctxt c ∘ (sort-lcis ∘ strings-to-lcis)

ctxt-at : (pos : ℕ) → ctxt → ctxt
ctxt-at pi Γ @ (mk-ctxt (fn , mn , _) _ si _) = foldr (flip ctxt-clear-symbol ∘ fst) Γ
  (flip filter (trie-mappings si) λ where
    (x , ci , fn' , pi') → fn =string fn' && posinfo-to-ℕ pi' > pi)

get-local-ctxt : ctxt → (pos : ℕ) → (local-ctxt : 𝕃 string) → ctxt
get-local-ctxt Γ pos = merge-lcis-ctxt (ctxt-at pos Γ)


{- Helpers -}

qualif-ed : {ed : exprd} → ctxt → ⟦ ed ⟧ → ⟦ ed ⟧
qualif-ed{TERM} = qualif-term
qualif-ed{TYPE} = qualif-type
qualif-ed{KIND} = qualif-kind
qualif-ed Γ e = e

expr-to-tv : ctxt → ({ed : exprd} → ⟦ ed ⟧ → ⟦ ed ⟧) → expr → string ⊎ tagged-val
expr-to-tv Γ f (, t) = inj₂ (to-string-tag "" Γ (f t))

qualif-expr : ctxt → expr → expr
qualif-expr Γ (,_ {ll} x) = , qualif-ed {language-level-to-exprd ll} Γ x

checked-with-no-errors : (maybe type × ctxt × spans) → maybe type
checked-with-no-errors (just T , _ , (regular-spans nothing _)) = just T
checked-with-no-errors _ = nothing

rewrite-expr' : ctxt → expr → term → term → 𝔹 → Σi language-level (λ p → language-level-lift p × ℕ × ℕ)
rewrite-expr' Γ (,_ {ll-term} t) t₁ t₂ b = ,
  rewrite-term (qualif-term Γ t) Γ empty-renamectxt b nothing t₁ t₂ 0
rewrite-expr' Γ (,_ {ll-type} T) t₁ t₂ b = ,
  rewrite-type (qualif-type Γ T) Γ empty-renamectxt b nothing t₁ t₂ 0
rewrite-expr' Γ (,_ {ll-kind} k) t₁ t₂ b = ,
  rewrite-kind (qualif-kind Γ k) Γ empty-renamectxt b nothing t₁ t₂ 0

rewrite-expr : ctxt → expr → term → term → 𝔹 → string ⊎ tagged-val
rewrite-expr Γ e t₁ t₂ b with rewrite-expr' Γ e t₁ t₂ b
...| , e' , 0 , _ = inj₁ "No rewrites could be performed"
...| , e' , n , _ = expr-to-tv Γ (λ x → x) (, e')


{- Command Executors -}

normalize-cmd : ctxt → (str ll pi hd do-erase : string) → 𝕃 string → string ⊎ tagged-val
normalize-cmd Γ str ll pi hd de ls =
  string-to-language-level - ll ! "language-level" ≫parse λ nt →
  string-to-ℕ - pi ! "natural number" ≫parse λ sp →
  string-to-𝔹 - hd ! "boolean" ≫parse λ is-hd →
  string-to-𝔹 - de ! "boolean" ≫parse λ do-e →
  let Γ' = get-local-ctxt Γ sp ls in
  parse-string nt - str ! ll ≫parse
  (expr-to-tv Γ' (λ t → hnf Γ' (unfold (~ is-hd) (~ is-hd) ff tt) (qualif-ed Γ' t) tt) ∘ ,_)

normalize-prompt : ctxt → (str hd : string) → string ⊎ tagged-val
normalize-prompt Γ str hd =
  string-to-𝔹 - hd ! "boolean" ≫parse λ is-hd →
  parse-try Γ - str ! ttk ≫parse
  expr-to-tv Γ (λ t → hnf Γ (unfold (~ is-hd) (~ is-hd) ff tt) (qualif-ed Γ t) tt)

erase-cmd : ctxt → (str ll pi : string) → 𝕃 string → string ⊎ tagged-val
erase-cmd Γ str ll pi ls =
  string-to-language-level - ll ! "language-level" ≫parse λ nt →
  string-to-ℕ - pi ! "natural number" ≫parse λ sp →
  let Γ' = get-local-ctxt Γ sp ls in
  parse-string nt - str ! ll ≫parse
  (expr-to-tv Γ' (qualif-ed Γ' ∘ erase) ∘ ,_)

erase-prompt : ctxt → (str : string) → string ⊎ tagged-val
erase-prompt Γ str =
  parse-try Γ - str ! ttk ≫parse
  expr-to-tv Γ (qualif-ed Γ ∘ erase)

br-cmd : ctxt → (str : string) → 𝕃 string → IO ⊤
br-cmd Γ str ls =
  let Γ' = merge-lcis-ctxt Γ ls in
  maybe-else
    (return (io-spans.spans-to-rope (io-spans.global-error "Parse error" nothing)))
    (λ s → s >>= return ∘ io-spans.spans-to-rope)
    (parse-try Γ' str ≫=maybe λ ex →
     h ex ≫=maybe λ m →
     just (m Γ' io-spans.empty-spans >>=
           return ∘ (snd ∘ snd))) >>=
  putRopeLn where
    h : expr → maybe (io-spans.spanM ⊤)
    h (,_ {ll-term} t) = just (untyped-term-spans t)
    h (,_ {ll-type} T) = just (untyped-type-spans T)
    h (,_ {ll-kind} k) = just (untyped-kind-spans k)

conv-cmd : ctxt → (ll str1 str2 : string) → 𝕃 string → string ⊎ string
conv-cmd Γ ll s1 s2 ls =
  let Γ' = merge-lcis-ctxt Γ ls in
  string-to-language-level - ll ! "language-level" ≫parse λ nt →
  parse-string nt - s1 ! ll ≫parse λ ex1 →
  parse-string nt - s2 ! ll ≫parse λ ex2 →
  h Γ' (, ex1) (, ex2)
  where
  expr-to-string : expr → string
  expr-to-string (,_ {ll-term} _) = "term"
  expr-to-string (,_ {ll-type} _) = "type"
  expr-to-string (,_ {ll-kind} _) = "kind"

  does-conv : ctxt → {ed : exprd} → ⟦ ed ⟧ → 𝔹 → string ⊎ string
  does-conv Γ x tt = inj₂ (rope-to-string (to-string Γ (erase x)))
  does-conv Γ x ff = inj₁ "Inconvertible"

  h : ctxt → expr → expr → string ⊎ string
  h Γ (,_ {ll-term} t₁) (,_ {ll-term} t₂) =
    does-conv Γ t₂ (conv-term Γ (qualif-term Γ t₁) (qualif-term Γ t₂))
  h Γ (,_ {ll-type} T₁) (,_ {ll-type} T₂) =
    does-conv Γ T₂ (conv-type Γ (qualif-type Γ T₁) (qualif-type Γ T₂))
  h Γ (,_ {ll-kind} k₁) (,_ {ll-kind} k₂) =
    does-conv Γ k₂ (conv-kind Γ (qualif-kind Γ k₁) (qualif-kind Γ k₂))
  h _ e1 e2 = inj₁ ("Mismatched language levels (\\\\\"" ^ s1 ^ "\\\\\" is a " ^
    expr-to-string e1 ^ " and \\\\\"" ^ s2 ^ "\\\\\" is a " ^ expr-to-string e2 ^ ")")

rewrite-cmd : ctxt → (span-str : string) → (input-str : string) → (use-hnf : string) → (local-ctxt : 𝕃 string) → string ⊎ tagged-val
rewrite-cmd Γ ss is hd ls =
  string-to-𝔹 - hd ! "boolean" ≫parse λ use-hnf →
  let Γ' = merge-lcis-ctxt Γ ls in
  parse-try Γ' - ss ! ttk ≫parse λ ss →
  parse-try Γ' - is ! ttk ≫parse λ where
  (,_ {ll-term} t) →
    checked-with-no-errors (check-term t nothing Γ' empty-spans)
      ! "Error when synthesizing a type for the input term" ≫error λ where
    (TpEq _ t₁ t₂ _) → rewrite-expr Γ' ss t₁ t₂ use-hnf
    _ → inj₁ "Synthesized a non-equational type from the input term"
  (,_ {ll-type} (TpEq _ t₁ t₂ _)) →
    rewrite-expr Γ' (qualif-expr Γ' ss) (qualif-term Γ' t₁) (qualif-term Γ' t₂) use-hnf
  (,_ {ll-type} T) → inj₁ "Expected the input expression to be a term, but got a type"
  (,_ {ll-kind} _) → inj₁ "Expected the input expression to be a term, but got a kind"

to-string-cmd : ctxt → string → string ⊎ tagged-val
to-string-cmd Γ s = parse-try Γ - s ! ttk ≫parse inj₂ ∘ h where
  h : expr → tagged-val
  h (,_ {pa} t) = to-string-tag {language-level-to-exprd pa} "" empty-ctxt t


{- Commands -}

tv-to-rope : string ⊎ tagged-val → rope
tv-to-rope (inj₁ s) = [[ "{\"error\":\"" ]] ⊹⊹ [[ s ]] ⊹⊹ [[ "\"}" ]]
tv-to-rope (inj₂ (_ , v , ts)) = [[ "{" ]] ⊹⊹ tagged-val-to-rope 0 ("value" , v , ts) ⊹⊹ [[ "}" ]]

interactive-cmd : 𝕃 string → toplevel-state → IO ⊤
interactive-cmd-h : ctxt → 𝕃 string → string ⊎ tagged-val
interactive-cmd ("br" :: input :: lc) ts = br-cmd (toplevel-state.Γ ts) input lc
interactive-cmd ls ts = putRopeLn (tv-to-rope (interactive-cmd-h (toplevel-state.Γ ts) ls))

-- Agda has some issue with pattern matching and eta-contracting,
-- which this showcases (calling this function causes Agda to crash at runtime).
-- This is somewhat similar to the bug I found several weeks ago,
-- so I believe that they have a common source.
test1 : string → string ⊎ tagged-val
test1 "" = inj₁ "empty"
test1 = inj₁ -- Doesn't work

test2 : string → string ⊎ tagged-val
test2 "" = inj₁ "empty"
test2 s = inj₁ s -- Works correctly

interactive-cmd-h _ ("test-agda-eta1" :: s :: []) = test1 s
interactive-cmd-h _ ("test-agda-eta2" :: s :: []) = test2 s
interactive-cmd-h Γ ("normalize" :: input :: ll :: sp :: head :: do-erase :: lc) =
  normalize-cmd Γ input ll sp head do-erase lc
interactive-cmd-h Γ ("erase" :: input :: ll :: sp :: lc) =
  erase-cmd Γ input ll sp lc
interactive-cmd-h Γ ("normalizePrompt" :: input :: head :: []) =
  normalize-prompt Γ input head
interactive-cmd-h Γ ("erasePrompt" :: input :: []) =
  erase-prompt Γ input
interactive-cmd-h Γ ("conv" :: ll :: ss :: is :: lc) =
  map⊎ (conv-cmd Γ ll ss is lc) (λ s → "" , [[ s ]] , [])
interactive-cmd-h Γ ("rewrite" :: ss :: is :: head :: lc) =
  rewrite-cmd Γ ss is head lc
interactive-cmd-h Γ ("to-string" :: s :: []) =
  to-string-cmd Γ s
interactive-cmd-h Γ cs = inj₁ ("Unknown interactive cmd: " ^ 𝕃-to-string (λ s → s) ", " cs)
