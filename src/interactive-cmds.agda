module interactive-cmds where

import parse
import run
open import lib
open import functions
open import cedille-types
open import conversion
open import ctxt
open import general-util
open import spans
open import syntax-util
open import to-string
open import toplevel-state
open import erased-spans
open import parser

{- General -}

maybee : ∀{A B : Set} → maybe A → B → (A → B) → B
maybee m n j = maybe-else n j m

maybe-or : ∀{ℓ}{A : Set ℓ} → maybe A → maybe A → maybe A
maybe-or m₁ m₂ = maybe-else m₂ just m₁

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

expr : Set
expr = Σi parseAs parseAs-lift

either-to-expr : {pa : parseAs} → Either string (parseAs-lift pa) → parsedExpr pa
either-to-expr (Left e) = nothing
either-to-expr (Right e) = just e

var-is-type : ctxt → var → 𝔹
var-is-type Γ v =
  (isJust (ctxt-lookup-type-var Γ v) || isJust (ctxt-lookup-type-var-def Γ v)) && ~
  (isJust (ctxt-lookup-term-var Γ v) || isJust (ctxt-lookup-term-var-def Γ v))

ll-disambiguate : ctxt → expr → expr
ll-disambiguate Γ e @ (,_ {parseAsTerm} (Var pi x)) =
  if var-is-type Γ x then , (TpVar pi x) else e
ll-disambiguate Γ e @ (,_ {parseAsTerm} (App t me t')) with ll-disambiguate Γ (, t)
...| ,_ {parseAsType} T = , (TpAppt T t')
...| _ = e
ll-disambiguate Γ e @ (,_ {parseAsTerm} (AppTp t T')) with ll-disambiguate Γ (, t)
...| ,_ {parseAsType} T = , (TpApp T T')
...| _ = e
ll-disambiguate Γ e = e

parse-string : (pa : parseAs) → string → parsedExpr pa
parse-string pa = either-to-expr ∘ h pa where
  h : (pa : parseAs) → string → Either string (parseAs-lift pa)
  h parseAsTerm = parseTerm
  h parseAsType = parseType
  h parseAsKind = parseKind
  h parseAsLiftingType = parseLiftingType


infixr 7 _≫nothing_
_≫nothing_ : ∀{ℓ}{A : Set ℓ} → maybe A → maybe A → maybe A
(nothing ≫nothing m₂) = m₂
(m₁ ≫nothing m₂) = m₁

parse-try : ctxt → string → maybe expr
parse-try Γ s = maybe-map (ll-disambiguate Γ) (
  maybe-map ,_ (parse-string parseAsTerm s) ≫nothing
  maybe-map ,_ (parse-string parseAsType s) ≫nothing
  maybe-map ,_ (parse-string parseAsKind s) ≫nothing
  maybe-map ,_ (parse-string parseAsLiftingType s))


qualif-ed : {ed : exprd} → ctxt → ⟦ ed ⟧ → ⟦ ed ⟧
qualif-ed{TERM} = qualif-term
qualif-ed{TYPE} = qualif-type
qualif-ed{KIND} = qualif-kind
qualif-ed Γ e = e

expr-to-tv : ctxt → ({ed : exprd} → ⟦ ed ⟧ → ⟦ ed ⟧) → expr → maybe tagged-val
expr-to-tv Γ f (, t) = just (to-string-tag "" Γ (f t))
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

parse-error-message : (failed-to-parse : string) → (as-a : string) → string × 𝔹
parse-error-message failed-to-parse as-a = "Failed to parse \"" ^ failed-to-parse ^ "\" as a " ^ as-a , ff

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

ctxt-set-cur-file : ctxt → string → ctxt
ctxt-set-cur-file (mk-ctxt (_ , ps , q) ss is os) fn = mk-ctxt (fn , ps , q) ss is os

parseAs-type-of : parseAs → parseAs
parseAs-type-of parseAsTerm = parseAsType
parseAs-type-of parseAsType = parseAsKind
parseAs-type-of pa = pa

merge-lci-ctxt : lci → (do-erase : 𝔹) → ctxt → ctxt
merge-lci-ctxt (mk-lci nt v t T fn pi) de Γ =
  maybe-else Γ (λ Γ → Γ) (string-to-parseAs nt ≫=maybe λ nt → parse-string (parseAs-type-of nt ) T ≫=maybe (h (parse-string nt t) ∘ ,_)) where
  h : {pa : parseAs} → parsedExpr pa → expr → maybe ctxt
  h {parseAsTerm} (just t) (,_ {parseAsType} T) = just (ctxt-term-def pi localScope v t T Γ)
  h {parseAsType} (just T) (,_ {parseAsKind} k) = just (ctxt-type-def pi localScope v T k Γ)
  h nothing (,_ {parseAsType} T) = just (ctxt-term-decl pi localScope v T Γ)
  h nothing (,_ {parseAsKind} k) = just (ctxt-type-decl pi localScope v k Γ)
  h _ _ = nothing

merge-lcis-ctxt : 𝕃 lci → (do-erase : 𝔹) → ctxt → ctxt
merge-lcis-ctxt (h :: t) de Γ = merge-lcis-ctxt t de (merge-lci-ctxt h de Γ)
merge-lcis-ctxt [] _ Γ = Γ
    
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

-- TODO: Use module name instead of filename
ctxt-at : (pos : ℕ) → (filename : string) → ctxt → ctxt
ctxt-at pos filename Γ @ (mk-ctxt _ _ si _) =
  ctxt-nyd-all (ctxt-set-cur-file Γ filename) (to-nyd si filename pos)
  where
    ctxt-nyd-all : ctxt → 𝕃 (sym-info × string) → ctxt
    ctxt-nyd-all Γ (((_ , (fn , _)) , v) :: t) = ctxt-nyd-all (ctxt-clear-symbol (ctxt-clear-symbol Γ v) (fn # v)) t
    ctxt-nyd-all Γ [] = Γ

get-local-ctxt : ctxt → (pos : ℕ) → (filename : string) →
                 (local-ctxt : 𝕃 string) → (do-erase : 𝔹) → ctxt
get-local-ctxt Γ pos filename local-ctxt de =
  merge-lcis-ctxt (strings-to-lcis local-ctxt) de (ctxt-at pos filename Γ)

{- Command Executors -}

normalize-cmd : ctxt → (str ll pi fn hd do-erase : string) → 𝕃 string → maybe tagged-val
normalize-cmd Γ str ll pi fn hd de ls =
  string-to-parseAs ll ≫=maybe λ nt →
  string-to-ℕ pi ≫=maybe λ sp →
  string-to-𝔹 hd ≫=maybe λ is-hd →
  string-to-𝔹 de ≫=maybe λ do-e →
  let Γ' = get-local-ctxt Γ sp fn ls do-e in
  parse-string nt str ≫=maybe
  (expr-to-tv Γ' (λ t → hnf Γ' (unfold (~ is-hd) ff ff) (qualif-ed Γ' t) tt) ∘ ,_)

normalize-prompt : ctxt → (str hd : string) → maybe tagged-val
normalize-prompt Γ str hd =
  string-to-𝔹 hd ≫=maybe λ is-hd →
  parse-try Γ str ≫=maybe expr-to-tv Γ (λ t → hnf Γ (unfold (~ is-hd) ff ff) (qualif-ed Γ t) tt)

erase-cmd : ctxt → (str ll pi fn : string) → 𝕃 string → maybe tagged-val
erase-cmd Γ str ll pi fn ls =
  string-to-parseAs ll ≫=maybe λ nt →
  string-to-ℕ pi ≫=maybe λ sp →
  let Γ' = get-local-ctxt Γ sp fn ls ff in
  parse-string nt str ≫=maybe
  (expr-to-tv Γ' (erase ∘ qualif-ed Γ') ∘ ,_)

erase-prompt : ctxt → (str : string) → maybe tagged-val
erase-prompt Γ str = parse-try Γ str ≫=maybe expr-to-tv Γ (erase ∘ qualif-ed Γ)

br-cmd : ctxt → (str fn : string) → 𝕃 string → IO ⊤
br-cmd Γ str fn ls =
  let Γ' = get-local-ctxt Γ 0 "missing" ls ff in
  putStreengLn (
  maybe-else (spans-to-streeng (global-error "Parse error" nothing)) spans-to-streeng (
  parse-try Γ' str ≫=maybe λ ex →
  h ex ≫=maybe λ m →
  just (snd (snd (m Γ' (regular-spans [])))))) where
  h : expr → maybe (spanM ⊤)
  h (,_ {parseAsTerm} t) = just (erased-term-spans t)
  h (,_ {parseAsType} T) = just (erased-type-spans T)
  h (,_ {parseAsKind} k) = just (erased-kind-spans k)
  h _ = nothing

conv-cmd : ctxt → (ll str1 str2 pi fn : string) → 𝕃 string → maybe string
conv-cmd Γ ll s1 s2 pi fn ls =
  let Γ' = get-local-ctxt Γ 0 "missing" ls ff in
  (string-to-ℕ pi ≫=maybe λ n →
   string-to-parseAs ll ≫=maybe λ nt →
   parse-string nt s1 ≫=maybe λ ex1 →
   parse-string nt s2 ≫=maybe λ ex2 →
   just (𝔹-to-string (h Γ' (, ex1) (, ex2)))) where
  h : ctxt → expr → expr → 𝔹
  h Γ (,_ {parseAsTerm} t₁) (,_ {parseAsTerm} t₂) = conv-term Γ t₁ t₂
  h Γ (,_ {parseAsType} T₁) (,_ {parseAsType} T₂) = conv-type Γ T₁ T₂
  h Γ (,_ {parseAsKind} k₁) (,_ {parseAsKind} k₂) = conv-kind Γ k₁ k₂
  h Γ (,_ {parseAsLiftingType} lT₁) (,_ {parseAsLiftingType} lT₂) = conv-liftingType Γ lT₁ lT₂
  h _ _ _ = ff

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

to-string-cmd : ctxt → string → maybe tagged-val
to-string-cmd Γ s = maybe-map h (parse-try Γ s) where
  h : expr → tagged-val
  h (,_ {pa} t) = to-string-tag {parseAs-to-exprd pa} "" empty-ctxt t


{- Commands -}

mtv-to-streeng : maybe tagged-val → streeng
mtv-to-streeng nothing = [[ "{\"error\":\"Error\"}" ]]
mtv-to-streeng (just (_ , v , ts)) = [[ "{" ]] ⊹⊹ tagged-val-to-streeng 0 ("value" , v , ts) ⊹⊹ [[ "}" ]]

interactive-cmd : 𝕃 string → toplevel-state → IO toplevel-state
interactive-cmd-h : ctxt → 𝕃 string → maybe tagged-val
interactive-cmd ("br" :: input :: fn :: lc) ts =
  br-cmd (toplevel-state.Γ ts) input fn lc >>
  return ts
interactive-cmd ls ts =
  putStreengLn (mtv-to-streeng (interactive-cmd-h (toplevel-state.Γ ts) ls)) >>
  return ts

interactive-cmd-h Γ ("normalize" :: input :: ll :: sp :: fn :: head :: do-erase :: lc) =
  normalize-cmd Γ input ll sp fn head do-erase lc
interactive-cmd-h Γ ("erase" :: input :: ll :: sp :: fn :: lc) =
  erase-cmd Γ input ll sp fn lc
interactive-cmd-h Γ ("normalizePrompt" :: input :: fn :: head :: []) =
  normalize-prompt Γ input head
interactive-cmd-h Γ ("erasePrompt" :: input :: fn :: []) =
  erase-prompt Γ input
interactive-cmd-h Γ ("conv" :: ll :: ss :: is :: sp :: fn :: lc) =
  conv-cmd Γ ll ss is sp fn lc ≫=maybe λ s → just ("" , [[ s ]] , [])
interactive-cmd-h Γ ("to-string" :: s :: []) =
  to-string-cmd Γ s
interactive-cmd-h Γ cs = nothing

