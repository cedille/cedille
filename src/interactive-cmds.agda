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
open import erased-spans options {IO}
open import parser
open import rewriting
open import rename
open import classify options {Id}
import spans options {IO} as io-spans

{- General -}

data parseAs : Set where
  parseAsTerm : parseAs
  parseAsType : parseAs
  parseAsKind : parseAs
  parseAsLiftingType : parseAs

parseAs-to-exprd : parseAs → exprd
parseAs-to-exprd parseAsTerm = TERM
parseAs-to-exprd parseAsType = TYPE
parseAs-to-exprd parseAsKind = KIND
parseAs-to-exprd parseAsLiftingType = LIFTINGTYPE

parseAs-lift : parseAs → Set
parseAs-lift = ⟦_⟧ ∘ parseAs-to-exprd
parsedExpr : (pa : parseAs) → Set
parsedExpr pa = maybe (parseAs-lift pa)

ttklt : string
ttklt = "term, type, kind, or lifting type"

expr : Set
expr = Σi parseAs parseAs-lift

either-to-expr : {pa : parseAs} → Either string (parseAs-lift pa) → parsedExpr pa
either-to-expr (Left e) = nothing
either-to-expr (Right e) = just e

var-is-type : ctxt → var → 𝔹
var-is-type Γ v = isJust (ctxt-lookup-type-var Γ v)

ll-disambiguate' : ctxt → term → expr
ll-disambiguate' Γ e @ (Var pi x) =
  if var-is-type Γ x then , TpVar pi x else , e
ll-disambiguate' Γ e @ (App t me t') =
  case ll-disambiguate' Γ t of λ where
    (,_ {parseAsType} T) → , TpAppt T t'
    _ → , e
ll-disambiguate' Γ e @ (AppTp t T') =
  case ll-disambiguate' Γ t of λ where
    (,_ {parseAsType} T) → , TpApp T T'
    _ → , e
ll-disambiguate' Γ e @ (Lam pi KeptLambda pi' v (SomeClass atk) t ) =
  case ll-disambiguate' Γ t of λ where
    (,_ {parseAsType} T) → , TpLambda pi pi' v atk T
    _ → , e
ll-disambiguate' Γ = ,_

ll-disambiguate : ctxt → expr → expr
ll-disambiguate Γ (,_ {parseAsTerm} t) = ll-disambiguate' Γ t
ll-disambiguate Γ e = e

parse-string : (pa : parseAs) → string → parsedExpr pa
parse-string pa = either-to-expr ∘ h pa where
  h : (pa : parseAs) → string → Either string (parseAs-lift pa)
  h parseAsTerm = parseTerm
  h parseAsType = parseType
  h parseAsKind = parseKind
  h parseAsLiftingType = parseLiftingType

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
  (maybe-map ,_ (parse-string parseAsTerm s) ≫nothing
   maybe-map ,_ (parse-string parseAsType s) ≫nothing
   maybe-map ,_ (parse-string parseAsKind s) ≫nothing
   maybe-map ,_ (parse-string parseAsLiftingType s))


qualif-ed : {ed : exprd} → ctxt → ⟦ ed ⟧ → ⟦ ed ⟧
qualif-ed{TERM} = qualif-term
qualif-ed{TYPE} = qualif-type
qualif-ed{KIND} = qualif-kind
qualif-ed Γ e = e

expr-to-tv : ctxt → ({ed : exprd} → ⟦ ed ⟧ → ⟦ ed ⟧) → expr → string ⊎ tagged-val
expr-to-tv Γ f (, t) = inj₂ (to-string-tag "" Γ (f t))

add-ws : 𝕃 char → 𝕃 char
add-ws (' ' :: lc) = ' ' :: lc
add-ws lc = ' ' :: lc

-- Makes the string more aesthetically pleasing by removing newlines,
-- replacing tabs with spaces, and removing unnecessary double whitespaces.
-- Also, interactive parsing fails if there are newlines anywhere or periods at the end.
pretty-string-h : 𝕃 char → 𝕃 char → 𝕃 char
pretty-string-h ('\n' :: rest) so-far = pretty-string-h rest (add-ws so-far)
pretty-string-h (' ' :: rest) so-far = pretty-string-h rest (add-ws so-far)
pretty-string-h ('\t' :: rest) so-far = pretty-string-h rest (add-ws so-far)
pretty-string-h (c :: rest) so-far = pretty-string-h rest (c :: so-far)
pretty-string-h [] so-far = reverse (remove-proceeding-ws-period so-far)
  where
    remove-proceeding-ws-period : 𝕃 char → 𝕃 char
    remove-proceeding-ws-period (' ' :: rest) = remove-proceeding-ws-period rest
    remove-proceeding-ws-period ('.' :: rest) = remove-proceeding-ws-period rest
    remove-proceeding-ws-period rest = rest

pretty-string : string → string
pretty-string str = 𝕃char-to-string (pretty-string-h (string-to-𝕃char str) [])

𝕃char-starts-with : 𝕃 char → 𝕃 char → 𝔹
𝕃char-starts-with (h1 :: t1) (h2 :: t2) = (h1 =char h2) && 𝕃char-starts-with t1 t2
𝕃char-starts-with [] (h :: t) = ff
𝕃char-starts-with _ _ = tt

string-to-𝔹 : string → maybe 𝔹
string-to-𝔹 "tt" = just tt
string-to-𝔹 "ff" = just ff
string-to-𝔹 _ = nothing

string-to-parseAs : string → maybe parseAs
string-to-parseAs "term" = just parseAsTerm
string-to-parseAs "type" = just parseAsType
string-to-parseAs "kind" = just parseAsKind
string-to-parseAs "liftingType" = just parseAsLiftingType
string-to-parseAs _ = nothing


{- Contextualization -}

data lci : Set where
  mk-lci : (ll : string) → (x : var) → (t : string) → (T : string) → (fn : string) → (pi : posinfo) → lci

strings-to-lcis : 𝕃 string → 𝕃 lci
strings-to-lcis ss = strings-to-lcis-h ss []
  where
    strings-to-lcis-h : 𝕃 string → 𝕃 lci → 𝕃 lci
    strings-to-lcis-h (ll :: x :: t :: T :: fn :: pi :: tl) items =
      strings-to-lcis-h tl (mk-lci ll x t T fn pi :: items)
    strings-to-lcis-h _ items = items

parseAs-type-of : parseAs → parseAs
parseAs-type-of parseAsTerm = parseAsType
parseAs-type-of parseAsType = parseAsKind
parseAs-type-of pa = pa

-- Adds local variables to the qualif so that their
-- types are correctly qualified in merge-lci-ctxt
merge-lcis-ctxth : 𝕃 lci → ctxt → ctxt
merge-lcis-ctxth (mk-lci _ v _ _ _ pi :: tl) (mk-ctxt (fn , mn , pms , q) ss is os) =
  merge-lcis-ctxth tl (mk-ctxt (fn , mn , pms , qualif-insert-params q (pi % v) v ParamsNil) ss is os)
merge-lcis-ctxth [] Γ = Γ

merge-lci-ctxt : lci → ctxt → ctxt
merge-lci-ctxt (mk-lci nt v t T fn pi) Γ =
  maybe-else Γ (λ Γ → Γ) (string-to-parseAs nt ≫=maybe λ nt → parse-string (parseAs-type-of nt ) T ≫=maybe (h (mp nt t) ∘ ,_)) where
  h : {pa : parseAs} → parsedExpr pa → expr → maybe ctxt
  h {parseAsTerm} (just t) (,_ {parseAsType} T) = just (ctxt-term-def pi localScope nonParamVar v t T Γ)
  h {parseAsType} (just T) (,_ {parseAsKind} k) = just (ctxt-type-def pi localScope nonParamVar v T k Γ)
  h nothing (,_ {parseAsType} T) = just (ctxt-term-decl pi localScope v T Γ)
  h nothing (,_ {parseAsKind} k) = just (ctxt-type-decl pi localScope v k Γ)
  h _ _ = nothing

  mp : (pa : parseAs) → string → parsedExpr pa
  mp pa "" = nothing
  mp = parse-string

merge-lcis-ctxt' : 𝕃 lci → ctxt → ctxt
merge-lcis-ctxt' (h :: t) Γ = merge-lcis-ctxt' t (merge-lci-ctxt h Γ)
merge-lcis-ctxt' [] Γ = Γ

merge-lcis-ctxt : 𝕃 string → ctxt → ctxt
merge-lcis-ctxt ls Γ = let lc = strings-to-lcis ls in
  merge-lcis-ctxt' lc (merge-lcis-ctxth lc Γ)

to-nyd-h : trie sym-info → string → ℕ → (so-far : 𝕃 (sym-info × string)) →
           (path : 𝕃 char) → 𝕃 (sym-info × string)
to-nyd-h (Node msi ((c , h) :: t)) fn pos sf path =
  to-nyd-h (Node msi t) fn pos (to-nyd-h h fn pos sf (c :: path)) path
to-nyd-h (Node (just (ci , fp , pi)) []) fn pos sf path =
  if (fp =string fn) && ((posinfo-to-ℕ pi) > pos)
    then (((ci , fp , pi) , (𝕃char-to-string (reverse path))) :: sf)
    else sf
to-nyd-h _ _ _ sf _ = sf

to-nyd : trie sym-info → (filename : string) → (pos : ℕ) → 𝕃 (sym-info × string)
to-nyd tr fn pos = to-nyd-h tr fn pos [] []

ctxt-at : (pos : ℕ) → ctxt → ctxt
ctxt-at pos Γ @ (mk-ctxt (fn , mn , _) _ si _) =
  ctxt-nyd-all Γ (to-nyd si fn pos)
  where
    ctxt-nyd-all : ctxt → 𝕃 (sym-info × string) → ctxt
    ctxt-nyd-all Γ ((_ , v) :: t) =
      ctxt-nyd-all (ctxt-clear-symbol (ctxt-clear-symbol Γ v) (mn # v)) t
    ctxt-nyd-all Γ [] = Γ

get-local-ctxt : ctxt → (pos : ℕ) → (local-ctxt : 𝕃 string) → ctxt
get-local-ctxt Γ pos local-ctxt = merge-lcis-ctxt local-ctxt (ctxt-at pos Γ)


rewrite-expr' : ctxt → expr → term → term → 𝔹 → Σi parseAs (λ p → parseAs-lift p × ℕ)
rewrite-expr' Γ (,_ {parseAsTerm} t) t₁ t₂ b = ,
  rewrite-term Γ empty-renamectxt b t₁ t₂ (qualif-term Γ t)
rewrite-expr' Γ (,_ {parseAsType} T) t₁ t₂ b = ,
  rewrite-type Γ empty-renamectxt b t₁ t₂ (qualif-type Γ T)
rewrite-expr' Γ (,_ {parseAsKind} k) t₁ t₂ b = ,
  rewrite-kind Γ empty-renamectxt b t₁ t₂ (qualif-kind Γ k)
rewrite-expr' Γ (,_ {parseAsLiftingType} lT) t₁ t₂ b = ,
  rewrite-liftingType Γ empty-renamectxt b t₁ t₂ (qualif-liftingType Γ lT)

rewrite-expr : ctxt → expr → term → term → 𝔹 → string ⊎ tagged-val
rewrite-expr Γ e t₁ t₂ b with rewrite-expr' Γ e t₁ t₂ b
...| , e' , 0 = inj₁ "No rewrites could be performed"
...| , e' , n = expr-to-tv Γ (λ x → x) (, e')

{- Command Executors -}

normalize-cmd : ctxt → (str ll pi hd do-erase : string) → 𝕃 string → string ⊎ tagged-val
normalize-cmd Γ str ll pi hd de ls =
  string-to-parseAs - ll ! "language-level" ≫parse λ nt →
  string-to-ℕ - pi ! "natural number" ≫parse λ sp →
  string-to-𝔹 - hd ! "boolean" ≫parse λ is-hd →
  string-to-𝔹 - de ! "boolean" ≫parse λ do-e →
  let Γ' = get-local-ctxt Γ sp ls in
  parse-string nt - str ! ll ≫parse
  (expr-to-tv Γ' (λ t → hnf Γ' (unfold (~ is-hd) (~ is-hd) ff) (qualif-ed Γ' t) tt) ∘ ,_)

normalize-prompt : ctxt → (str hd : string) → string ⊎ tagged-val
normalize-prompt Γ str hd =
  string-to-𝔹 - hd ! "boolean" ≫parse λ is-hd →
  parse-try Γ - str ! ttklt ≫parse
  expr-to-tv Γ (λ t → hnf Γ (unfold (~ is-hd) (~ is-hd) ff) (qualif-ed Γ t) tt)

erase-cmd : ctxt → (str ll pi : string) → 𝕃 string → string ⊎ tagged-val
erase-cmd Γ str ll pi ls =
  string-to-parseAs - ll ! "language-level" ≫parse λ nt →
  string-to-ℕ - pi ! "natural number" ≫parse λ sp →
  let Γ' = get-local-ctxt Γ sp ls in
  parse-string nt - str ! ll ≫parse
  (expr-to-tv Γ' (erase ∘ qualif-ed Γ') ∘ ,_)

erase-prompt : ctxt → (str : string) → string ⊎ tagged-val
erase-prompt Γ str =
  parse-try Γ - str ! ttklt ≫parse
  expr-to-tv Γ (erase ∘ qualif-ed Γ)

br-cmd : ctxt → (str : string) → 𝕃 string → IO ⊤
br-cmd Γ str ls =
  let Γ' = merge-lcis-ctxt ls Γ in
  maybe-else
    (return (io-spans.spans-to-rope (io-spans.global-error "Parse error" nothing)))
    (λ s → s >>= return ∘ io-spans.spans-to-rope)
    (parse-try Γ' str ≫=maybe λ ex →
     h ex ≫=maybe λ m →
     just (m Γ' io-spans.empty-spans >>=
           return ∘ (snd ∘ snd))) >>=
  putRopeLn where
    h : expr → maybe (io-spans.spanM ⊤)
    h (,_ {parseAsTerm} t) = just (erased-term-spans t)
    h (,_ {parseAsType} T) = just (erased-type-spans T)
    h (,_ {parseAsKind} k) = just (erased-kind-spans k)
    h _ = nothing

conv-cmd : ctxt → (ll str1 str2 : string) → 𝕃 string → string ⊎ string
conv-cmd Γ ll s1 s2 ls =
  let Γ' = merge-lcis-ctxt ls Γ in
  string-to-parseAs - ll ! "language-level" ≫parse λ nt →
  parse-string nt - s1 ! ll ≫parse λ ex1 →
  parse-string nt - s2 ! ll ≫parse λ ex2 →
  h Γ' (, ex1) (, ex2)
  where
  expr-to-string : expr → string
  expr-to-string (,_ {parseAsTerm} _) = "term"
  expr-to-string (,_ {parseAsType} _) = "type"
  expr-to-string (,_ {parseAsKind} _) = "kind"
  expr-to-string (,_ {parseAsLiftingType} _) = "lifting type"

  does-conv : ctxt → {ed : exprd} → ⟦ ed ⟧ → 𝔹 → string ⊎ string
  does-conv Γ x tt = inj₂ (rope-to-string (to-string Γ (erase x)))
  does-conv Γ x ff = inj₁ "Inconvertible"

  h : ctxt → expr → expr → string ⊎ string
  h Γ (,_ {parseAsTerm} t₁) (,_ {parseAsTerm} t₂) =
    does-conv Γ t₂ (conv-term Γ (qualif-term Γ t₁) (qualif-term Γ t₂))
  h Γ (,_ {parseAsType} T₁) (,_ {parseAsType} T₂) =
    does-conv Γ T₂ (conv-type Γ (qualif-type Γ T₁) (qualif-type Γ T₂))
  h Γ (,_ {parseAsKind} k₁) (,_ {parseAsKind} k₂) =
    does-conv Γ k₂ (conv-kind Γ (qualif-kind Γ k₁) (qualif-kind Γ k₂))
  h Γ (,_ {parseAsLiftingType} lT₁) (,_ {parseAsLiftingType} lT₂) =
    does-conv Γ lT₂ (conv-liftingType Γ (qualif-liftingType Γ lT₁) (qualif-liftingType Γ lT₂))
  h _ e1 e2 = inj₁ ("Mismatched language levels (\\\\\"" ^ s1 ^ "\\\\\" is a " ^
    expr-to-string e1 ^ " and \\\\\"" ^ s2 ^ "\\\\\" is a " ^ expr-to-string e2 ^ ")")

qualif-expr : ctxt → expr → expr
qualif-expr Γ (,_ {parseAsTerm} t) = , qualif-term Γ t
qualif-expr Γ (,_ {parseAsType} T) = , qualif-type Γ T
qualif-expr Γ (,_ {parseAsKind} k) = , qualif-kind Γ k
qualif-expr Γ (,_ {parseAsLiftingType} lT) = , qualif-liftingType Γ lT

checked-with-no-errors : (maybe type × ctxt × spans) → maybe type
checked-with-no-errors (just T , _ , (regular-spans nothing _)) = just T
checked-with-no-errors _ = nothing

rewrite-cmd : ctxt → (span-str : string) → (input-str : string) → (use-hnf : string) → (local-ctxt : 𝕃 string) → string ⊎ tagged-val
rewrite-cmd Γ ss is hd lc =
  string-to-𝔹 - hd ! "boolean" ≫parse λ use-hnf →
  let Γ' = merge-lcis-ctxt lc Γ in
  parse-try Γ' - ss ! ttklt ≫parse λ ss →
  parse-try Γ' - is ! ttklt ≫parse λ where
  (,_ {parseAsTerm} t) →
    checked-with-no-errors (check-term t nothing Γ' empty-spans)
      ! "Error when synthesizing a type for the input term" ≫error λ where
    (TpEq t₁ t₂) → rewrite-expr Γ' ss t₁ t₂ use-hnf
    _ → inj₁ "Synthesized a non-equational type from the input term"
  (,_ {parseAsType} (TpEq t₁ t₂)) →
    rewrite-expr Γ' (qualif-expr Γ' ss) (qualif-term Γ' t₁) (qualif-term Γ' t₂) use-hnf
  (,_ {parseAsType} T) → inj₁ "Expected the input expression to be a term, but got a type"
  (,_ {parseAsKind} _) → inj₁ "Expected the input expression to be a term, but got a kind"
  (,_ {parseAsLiftingType} _) → inj₁ "Expected the input expression to be a term or a type, but got a lifting type"

to-string-cmd : ctxt → string → string ⊎ tagged-val
to-string-cmd Γ s = parse-try Γ - s ! ttklt ≫parse inj₂ ∘ h where
  h : expr → tagged-val
  h (,_ {pa} t) = to-string-tag {parseAs-to-exprd pa} "" empty-ctxt t


{- Commands -}

tv-to-rope : string ⊎ tagged-val → rope
tv-to-rope (inj₁ s) = [[ "{\"error\":\"" ]] ⊹⊹ [[ s ]] ⊹⊹ [[ "\"}" ]]
tv-to-rope (inj₂ (_ , v , ts)) = [[ "{" ]] ⊹⊹ tagged-val-to-rope 0 ("value" , v , ts) ⊹⊹ [[ "}" ]]

interactive-cmd : 𝕃 string → toplevel-state → IO toplevel-state
interactive-cmd-h : ctxt → 𝕃 string → string ⊎ tagged-val
interactive-cmd ("br" :: input :: lc) ts =
  br-cmd (toplevel-state.Γ ts) input lc >>
  return ts
interactive-cmd ls ts =
  putRopeLn (tv-to-rope (interactive-cmd-h (toplevel-state.Γ ts) ls)) >>
  return ts

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

{-
-- Handy debugging function
tree-map : ({ed : exprd} → ⟦ ed ⟧ → ⟦ ed ⟧) → {ed : exprd} → ⟦ ed ⟧ → ⟦ ed ⟧
tree-map-tk : ({ed : exprd} → ⟦ ed ⟧ → ⟦ ed ⟧) → tk → tk
tree-map-optTerm : ({ed : exprd} → ⟦ ed ⟧ → ⟦ ed ⟧) → optTerm → optTerm
tree-map-optType : ({ed : exprd} → ⟦ ed ⟧ → ⟦ ed ⟧) → optType → optType
tree-map-maybeAtype : ({ed : exprd} → ⟦ ed ⟧ → ⟦ ed ⟧) → maybeAtype → maybeAtype
tree-map-optClass : ({ed : exprd} → ⟦ ed ⟧ → ⟦ ed ⟧) → optClass → optClass
tree-map-maybeCheckType : ({ed : exprd} → ⟦ ed ⟧ → ⟦ ed ⟧) → maybeCheckType → maybeCheckType
tree-map-defTermOrType : ({ed : exprd} → ⟦ ed ⟧ → ⟦ ed ⟧) → defTermOrType → defTermOrType
tree-map-lterms : ({ed : exprd} → ⟦ ed ⟧ → ⟦ ed ⟧) → lterms → lterms
tree-map-args : ({ed : exprd} → ⟦ ed ⟧ → ⟦ ed ⟧) → args → args
tree-map-tk f (Tkt T) = Tkt (tree-map f T)
tree-map-tk f (Tkk k) = Tkk (tree-map f k)
tree-map-optTerm f NoTerm = NoTerm
tree-map-optTerm f (SomeTerm t pi) = SomeTerm (tree-map f t) pi
tree-map-optType f NoType = NoType
tree-map-optType f (SomeType T) = SomeType (tree-map f T)
tree-map-maybeAtype f NoAtype = NoAtype
tree-map-maybeAtype f (Atype t) = Atype (tree-map f t)
tree-map-optClass f NoClass = NoClass
tree-map-optClass f (SomeClass atk) = SomeClass (tree-map-tk f atk)
tree-map-maybeCheckType f NoCheckType = NoCheckType
tree-map-maybeCheckType f (Type T) = Type (tree-map f T)
tree-map-defTermOrType f (DefTerm pi v mT t) = DefTerm pi v (tree-map-maybeCheckType f mT) (tree-map f t)
tree-map-defTermOrType f (DefType pi v k T) = DefType pi v (tree-map f k) (tree-map f T)
tree-map-lterms f (LtermsNil pi) = LtermsNil pi
tree-map-lterms f (LtermsCons me t lts) = LtermsCons me (tree-map f t) (tree-map-lterms f lts)
tree-map-args f (ArgsNil pi) = ArgsNil pi
tree-map-args f (ArgsCons a as) = ArgsCons (f a) (tree-map-args f as)


tree-map f {TERM} (App t me t') = f (App (tree-map f t) me (tree-map f t'))
tree-map f {TERM} (AppTp t T) = f (AppTp (tree-map f t) (tree-map f T))
tree-map f {TERM} (Beta pi ot) = f (Beta pi (tree-map-optTerm f ot)) where
tree-map f {TERM} (Chi pi mT t) = f (Chi pi (tree-map-maybeAtype f mT) (tree-map f t))
tree-map f {TERM} (Epsilon pi lr' m t) = f (Epsilon pi lr' m (tree-map f t))
tree-map f {TERM} (Hole pi) = f (Hole pi)
tree-map f {TERM} (IotaPair pi t t' pi') = f (IotaPair pi (tree-map f t) (tree-map f t') pi')
tree-map f {TERM} (IotaProj t n pi) = f (IotaProj (tree-map f t) n pi)
tree-map f {TERM} (Lam pi l pi' x oc t) = f (Lam pi l pi' x (tree-map-optClass f oc) (tree-map f t))
tree-map f {TERM} (Let pi dtT t) = f (Let pi (tree-map-defTermOrType f dtT) (tree-map f t))
tree-map f {TERM} (Parens pi t pi') = f (Parens pi (tree-map f t) pi')
tree-map f {TERM} (Phi pi eq t t' pi') = f (Phi pi (tree-map f eq) (tree-map f t) (tree-map f t') pi')
tree-map f {TERM} (Rho pi r eq t) = f (Rho pi r (tree-map f eq) (tree-map f t))
tree-map f {TERM} (Sigma pi t) = f (Sigma pi (tree-map f t))
tree-map f {TERM} (Theta pi θ t lts) = f (Theta pi θ (tree-map f t) (tree-map-lterms f lts))
tree-map f {TERM} (Var pi x) = f (Var pi x)
tree-map f {TYPE} (Abs pi b pi' x atk T) = f (Abs pi b pi' x (tree-map-tk f atk) (tree-map f T))
tree-map f {TYPE} (Iota pi pi' x oT T) = f (Iota pi pi' x (tree-map-optType f oT) (tree-map f T))
tree-map f {TYPE} (Lft pi pi' x t lT) = f (Lft pi pi' x (tree-map f t) (tree-map f lT))
tree-map f {TYPE} (NoSpans T pi) = f (NoSpans (tree-map f T) pi)
tree-map f {TYPE} (TpApp T T') = f (TpApp (tree-map f T) (tree-map f T'))
tree-map f {TYPE} (TpAppt T t) = f (TpAppt (tree-map f T) (tree-map f t))
tree-map f {TYPE} (TpArrow T a T') = f (TpArrow (tree-map f T) a (tree-map f T'))
tree-map f {TYPE} (TpEq t t') = f (TpEq (tree-map f t) (tree-map f t'))
tree-map f {TYPE} (TpHole pi) = f (TpHole pi)
tree-map f {TYPE} (TpLambda pi pi' x atk T) = f (TpLambda pi pi' x (tree-map-tk f atk) (tree-map f T))
tree-map f {TYPE} (TpParens pi T pi') = f (TpParens pi (tree-map f T) pi')
tree-map f {TYPE} (TpVar pi x) = f (TpVar pi x)
tree-map f {KIND} (KndArrow k k') = f (KndArrow (tree-map f k) (tree-map f k'))
tree-map f {KIND} (KndParens pi k pi') = f (KndParens pi (tree-map f k) pi')
tree-map f {KIND} (KndPi pi pi' x atk k) = f (KndPi pi pi' x (tree-map-tk f atk) (tree-map f k))
tree-map f {KIND} (KndTpArrow T k) = f (KndTpArrow (tree-map f T) (tree-map f k))
tree-map f {KIND} (KndVar pi x as) = f (KndVar pi x (tree-map-args f as))
tree-map f {KIND} (Star pi) = f (Star pi)
tree-map f {LIFTINGTYPE} (LiftArrow lT lT') = f (LiftArrow (tree-map f lT) (tree-map f lT'))
tree-map f {LIFTINGTYPE} (LiftParens pi lT pi') = f (LiftParens pi (tree-map f lT) pi')
tree-map f {LIFTINGTYPE} (LiftPi pi x T lT) = f (LiftPi pi x (tree-map f T) (tree-map f lT))
tree-map f {LIFTINGTYPE} (LiftStar pi) = f (LiftStar pi)
tree-map f {LIFTINGTYPE} (LiftTpArrow T lT) = f (LiftTpArrow (tree-map f T) (tree-map f lT))
tree-map f {QUALIF} x = f x
tree-map f {ARG} x = f x
-}
