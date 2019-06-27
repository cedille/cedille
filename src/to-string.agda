import cedille-options

module to-string (options : cedille-options.options) where

open import cedille-types
open import constants
open import syntax-util
open import ctxt
open import rename
open import general-util
open import datatype-functions
open import type-util
open import free-vars
open import json

data expr-side : Set where
  left : expr-side
  right : expr-side
  neither : expr-side

not-left : expr-side → 𝔹
not-left left = ff
not-left _ = tt
not-right : expr-side → 𝔹
not-right right = ff
not-right _ = tt

exprd-eq : exprd → exprd → 𝔹
exprd-eq TERM TERM = tt
exprd-eq TYPE TYPE = tt
exprd-eq KIND KIND = tt
exprd-eq _ _ = ff

is-eq-op : {ed : exprd} → ⟦ ed ⟧ → 𝔹
is-eq-op{TERM} (Sigma _) = tt
is-eq-op{TERM} (Rho _ _ _ _) = tt
is-eq-op{TERM} (Phi _ _ _) = tt
is-eq-op{TERM} (Delta _ _) = tt
is-eq-op _ = ff

pattern arrow-var = "_arrow_"
pattern TpArrow tp me tp' = TpAbs me arrow-var (Tkt tp) tp'
pattern KdArrow tk kd = KdAbs arrow-var tk kd

is-arrow : {ed : exprd} → ⟦ ed ⟧ → 𝔹
is-arrow {TYPE} (TpArrow _ _ _) = tt
is-arrow {KIND} (KdArrow _ _) = tt
is-arrow _ = ff

is-type-level-app : ∀ {ed} → ⟦ ed ⟧ → 𝔹
is-type-level-app {TYPE} (TpApp T tT) = tt
is-type-level-app _ = ff

no-parens : {ed : exprd} → {ed' : exprd} → ⟦ ed ⟧ → ⟦ ed' ⟧ → expr-side → 𝔹
no-parens {TYPE} {TYPE} (TpAbs _ _ _ _) (TpArrow _ _ _) left = ff
no-parens {TYPE} {TYPE} (TpIota _ _ _) (TpArrow _ _ _) left = ff
no-parens {KIND} {KIND} (KdAbs _ _ _) (KdArrow _ _) left = ff
no-parens {TYPE} {KIND} (TpAbs _ _ _ _) (KdArrow _ _) left = ff
no-parens {TYPE} {KIND} (TpIota _ _ _) (KdArrow _ _) left = ff
no-parens {_} {TERM} _ (IotaPair t₁ t₂ x Tₓ) lr = tt
no-parens {_} {TYPE} _ (TpEq t₁ t₂) lr = tt
no-parens {_} {TERM} _ (Beta ot ot') lr = tt
no-parens {_} {TERM} _ (Phi tₑ t₁ t₂) lr = not-left lr
no-parens {_} {TERM} _ (Rho _ _ _ _) right = tt
no-parens {_} {TERM} _ (Delta _ _) right = tt
no-parens {_} {TERM} _ (LetTm _ _ _ _ _) lr = tt
no-parens {_} {TERM} _ (LetTp _ _ _ _) lr = tt
no-parens {_} {TERM} _ (Lam _ _ _ _) lr = tt
no-parens {_} {TERM} _ (Mu _ _ _ _ _) right = tt
no-parens {_} {TYPE} _ (TpLam _ _ _) lr = tt
no-parens {_} {TYPE} _ (TpAbs _ _ _ _) lr = tt
no-parens {_} {KIND} _ (KdAbs _ _ _) neither = tt
no-parens {_} {TYPE} _ (TpIota _ _ _) lr = tt
no-parens {TERM} {_} (App t t') p lr = ff
no-parens {TERM} {_} (AppE t tT) p lr = ff
no-parens {TERM} {_} (Beta ot ot') p lr = tt
no-parens {TERM} {_} (Delta T t) p lr = ff
no-parens {TERM} {_} (Hole pi) p lr = tt
no-parens {TERM} {_} (IotaPair t₁ t₂ x Tₓ) p lr = tt
no-parens {TERM} {_} (IotaProj t n) p lr = tt
no-parens {TERM} {_} (Lam me x tk? t) p lr = ff
no-parens {TERM} {_} (LetTm me x T t t') p lr = ff
no-parens {TERM} {_} (LetTp x T t t') p lr = ff
no-parens {TERM} {_} (Phi tₑ t₁ t₂) p lr = ff
no-parens {TERM} {_} (Rho tₑ x Tₓ t) p lr = ff
no-parens {TERM} {_} (Sigma t) p lr = is-eq-op p
no-parens {TERM} {_} (Var x) p lr = tt
no-parens {TERM} {_} (Mu _ _ _ _ _) p lr = ff
no-parens {TYPE} {e} (TpAbs me x tk T) p lr = exprd-eq e TYPE && is-arrow p && not-left lr
no-parens {TYPE} {_} (TpIota x T₁ T₂) p lr = ff
no-parens {TYPE} {_} (TpApp T tT) p lr = is-arrow p || (is-type-level-app p && not-right lr)
no-parens {TYPE} {_} (TpEq t₁ t₂) p lr = tt
no-parens {TYPE} {_} (TpHole pi) p lr = tt
no-parens {TYPE} {_} (TpLam x tk T) p lr = ff
no-parens {TYPE} {_} (TpVar x) p lr = tt
no-parens {KIND} {_} (KdAbs x tk k) p lr = is-arrow p && not-left lr
no-parens {KIND} {_} (KdHole pi) p lr = tt
no-parens {KIND} {_} KdStar p lr = tt

pattern ced-ops-drop-spine = cedille-options.options.mk-options _ _ _ _ ff _ _ _ ff _
pattern ced-ops-conv-arr = cedille-options.options.mk-options _ _ _ _ _ _ _ _ ff _
pattern ced-ops-conv-abs = cedille-options.options.mk-options _ _ _ _ _ _ _ _ tt _

drop-spine : cedille-options.options → {ed : exprd} → ctxt → ⟦ ed ⟧ → ⟦ ed ⟧
drop-spine ops @ ced-ops-drop-spine = h
  where
  drop-mod-argse : (mod : args) → (actual : args) → args
  drop-mod-argse (ArgE _ :: asₘ) (ArgE _ :: asₐ) = drop-mod-argse asₘ asₐ
  drop-mod-argse (Arg _ :: asₘ) (Arg t :: asₐ) = drop-mod-argse asₘ asₐ
  drop-mod-argse (_ :: asₘ) asₐ@(Arg t :: _) = drop-mod-argse asₘ asₐ
  -- ^ Relevant term arg, so wait until we find its corresponding relevant module arg ^
  drop-mod-argse _ asₐ = asₐ

  drop-mod-args-term : ctxt → var × args → term
  drop-mod-args-term Γ (v , as) =
    let uqv = unqual-all (ctxt-get-qualif Γ) v in
    flip recompose-apps (Var uqv) $
      maybe-else' (maybe-if (~ v =string uqv) >>
                   ctxt-get-qi Γ uqv)
        as λ qi → drop-mod-argse (snd qi) as

  drop-mod-args-type : ctxt → var × 𝕃 tmtp → type
  drop-mod-args-type Γ (v , as) =
    let uqv = unqual-all (ctxt-get-qualif Γ) v in
    flip recompose-tpapps (TpVar uqv) $
      maybe-else' (maybe-if (~ v =string uqv) >>
                   ctxt-qualif-args-length Γ NotErased uqv)
        as λ n → drop n as

  h : {ed : exprd} → ctxt → ⟦ ed ⟧ → ⟦ ed ⟧
  h {TERM} Γ t = maybe-else' (decompose-var-headed t) t (drop-mod-args-term Γ)
  h {TYPE} Γ T = maybe-else' (decompose-tpvar-headed T) T (drop-mod-args-type Γ)
  h Γ x = x
drop-spine ops Γ x = x

to-string-rewrite : {ed : exprd} → ctxt → cedille-options.options → ⟦ ed ⟧ → Σi exprd ⟦_⟧
to-string-rewrite{TYPE} Γ ced-ops-conv-arr (TpAbs me x (Tkt T) T') = , TpAbs me (if is-free-in x T' then x else arrow-var) (Tkt T) T'
to-string-rewrite{KIND} Γ ced-ops-conv-arr (KdAbs x tk k) = , KdAbs (if is-free-in x k then x else arrow-var) tk k
to-string-rewrite{TERM} Γ ops (Sigma t) with to-string-rewrite Γ ops t
...| ,_ {TERM} (Sigma t') = , t'
...| t? = , Sigma t
to-string-rewrite Γ ops x = , drop-spine ops Γ x


-------------------------------

open import pretty

use-newlines : 𝔹
use-newlines =
  ~ iszero (cedille-options.options.pretty-print-columns options)
  &&        cedille-options.options.pretty-print         options

doc-to-rope : DOC → rope
doc-to-rope = if use-newlines
  then pretty (cedille-options.options.pretty-print-columns options)
  else flatten-out

strM : Set
strM = {ed : exprd} → DOC → ℕ → 𝕃 tag → ctxt → maybe ⟦ ed ⟧ → expr-side → DOC × ℕ × 𝕃 tag

strEmpty : strM
strEmpty s n ts Γ pe lr = s , n , ts

to-stringh : {ed : exprd} → ⟦ ed ⟧ → strM

strM-Γ : (ctxt → strM) → strM
strM-Γ f s n ts Γ = f Γ s n ts Γ

infixr 2 _>>str_
  

_>>str_ : strM → strM → strM
(m >>str m') s n ts Γ pe lr with m s n ts Γ pe lr
(m >>str m') s n ts Γ pe lr | s' , n' , ts' = m' s' n' ts' Γ pe lr

strAdd : string → strM
strAdd s s' n ts Γ pe lr = s' <> TEXT [[ s ]] , n + string-length s , ts

strLine : strM
strLine s n ts Γ pe lr = s <> LINE , suc n , ts

strNest : ℕ → strM → strM
strNest i m s n ts Γ pe lr with m nil n ts Γ pe lr
...| s' , n' , ts' = s <> nest i s' , n' , ts'


strFold' : (ℕ → ℕ) → {ed : exprd} → 𝕃 (ℕ × strM) → ℕ → 𝕃 tag → ctxt → maybe ⟦ ed ⟧ → expr-side → 𝕃 (ℕ × DOC) × ℕ × 𝕃 tag
strFold' l [] n ts Γ pe lr = [] , n , ts
strFold' l ((i , x) :: []) n ts Γ pe lr with x nil n ts Γ pe lr
...| sₓ , nₓ , tsₓ = [ i , sₓ ] , nₓ , tsₓ
strFold' l ((i , x) :: xs) n ts Γ pe lr with x nil n ts Γ pe lr
...| sₓ , nₓ , tsₓ with strFold' l xs (l nₓ) tsₓ Γ pe lr
...| sₓₛ , nₓₛ , tsₓₛ = (i , sₓ) :: sₓₛ , nₓₛ , tsₓₛ

strFold : (ℕ → ℕ) → (𝕃 (ℕ × DOC) → DOC) → 𝕃 (ℕ × strM) → strM
strFold l f ms s n ts Γ pe lr with strFold' l ms n ts Γ pe lr
...| s' , n' , ts' = s <> f s' , n' , ts'

strFoldi : ℕ → (ℕ → ℕ) → (𝕃 DOC → DOC) → 𝕃 strM → strM
strFoldi i l f = strNest i ∘' strFold suc (f ∘' map snd) ∘' map (_,_ 0)

-- Either fit all args on one line, or give each their own line
strList : ℕ → 𝕃 strM → strM
strList i = strFoldi i suc λ ms → flatten (spread ms) :<|> stack ms

-- Fit as many args on each line as possible
-- (n = number of strM args)
-- (𝕃 strM so that optional args (nil) are possible)
strBreak : (n : ℕ) → fold n strM λ X → ℕ → 𝕃 strM → X
strBreak = h [] where
  h : 𝕃 (ℕ × strM) → (n : ℕ) → fold n strM λ X → ℕ → 𝕃 strM → X
  h ms (suc n) i m = h (map (_,_ i) m ++ ms) n
  h ms zero = strFold suc filln $ reverse ms

strBracket : char → strM → char → strM
strBracket l m r s n ts Γ pe lr with m nil (suc (suc n)) ts Γ pe lr
...| s' , n' , ts' = s <> bracket (char-to-string l) s' (char-to-string r) , suc (suc n') , ts'

strΓ' : defScope → var → strM → strM
strΓ' ds v m s n ts Γ@(mk-ctxt (fn , mn , ps , q) syms i Δ) pe =
  let gl = ds iff globalScope
      v' = if gl then (mn # v) else v in
  m s n ts (mk-ctxt
      (fn , mn , ps , qualif-insert-params q v' (unqual-local v) (if gl then ps else []))
      syms (trie-insert i v' (var-decl , ("missing" , "missing"))) Δ) pe

strΓ : var → strM → strM
strΓ x m s n ts Γ = m s n ts (ctxt-var-decl x Γ)

ctxt-get-file-id : ctxt → (filename : string) → ℕ
ctxt-get-file-id (mk-ctxt mod (syms , mn-fn , mn-ps , ids , id) is Δ) =
  trie-lookup-else 0 ids

make-loc-tag : ctxt → (filename start-to end-to : string) → (start-from end-from : ℕ) → tag
make-loc-tag Γ fn s e = make-tag "loc"
  (("fn" , json-nat (ctxt-get-file-id Γ fn)) ::
   ("s" , json-raw [[ s ]]) :: ("e" , json-raw [[ e ]]) :: [])

var-loc-tag : ctxt → location → var → 𝕃 (string × 𝕃 tag)
var-loc-tag Γ ("missing" , "missing") x = []
var-loc-tag Γ ("" , _) x = []
var-loc-tag Γ (_ , "") x = []
var-loc-tag Γ (fn , pi) x =
  let fn-tag = "fn" , json-nat (ctxt-get-file-id Γ fn)
      s-tag = "s" , json-raw [[ pi ]]
      e-tag = "e" , json-raw [[ posinfo-plus-str pi x ]] in
  [ "loc" , fn-tag :: s-tag :: e-tag :: [] ]

var-tags : ctxt → var → var → 𝕃 (string × 𝕃 tag)
var-tags Γ qv uqv =
  (if qv =string qualif-var Γ uqv then id else ("shadowed" , []) ::_)
  (var-loc-tag Γ (ctxt-var-location Γ qv) uqv)

strAddTags : string → 𝕃 (string × 𝕃 tag) → strM
strAddTags sₙ tsₙ sₒ n tsₒ Γ pe lr =
  let n' = n + string-length sₙ in
  sₒ <> TEXT [[ sₙ ]] , n' , map (uncurry λ k vs → make-tag k vs n n') tsₙ ++ tsₒ

strVar : var → strM
strVar v = strM-Γ λ Γ →
  let uqv = unqual-local v -- $ unqual-all (ctxt-get-qualif Γ) v
      uqv' = if cedille-options.options.show-qualified-vars options then v else uqv in
  strAddTags uqv' (var-tags Γ (qualif-var Γ v) uqv)

strKvar : var → strM
strKvar v = strM-Γ λ Γ → strVar (unqual-all (ctxt-get-qualif Γ) v)

-- Only necessary to unqual-local because of module parameters
strBvar : var → (class body : strM) → strM
strBvar v cm bm = strAdd (unqual-local v) >>str cm >>str strΓ' localScope v bm

strMetaVar : var → span-location → strM
strMetaVar x (fn , pi , pi') s n ts Γ pe lr =
  let n' = n + string-length x in
  s <> TEXT [[ x ]] , n' , make-loc-tag Γ fn pi pi' n n' :: ts


{-# TERMINATING #-}
term-to-stringh : term → strM
type-to-stringh : type → strM
kind-to-stringh : kind → strM
tk-to-stringh : tpkd → strM
ctr-to-string : ctr → strM
case-to-string : case → strM
cases-to-string : cases → strM
caseArgs-to-string : case-args → strM → strM

params-to-string : params → strM
params-to-string' : strM → params → strM
params-to-string'' : params → strM → strM 
optTerm-to-string : maybe term → char → char → 𝕃 strM
optClass-to-string : maybe tpkd → strM
optType-to-string : maybe char → maybe type → 𝕃 strM
arg-to-string : arg → strM
args-to-string : args → strM
binder-to-string : erased? → string
lam-to-string : erased? → string
arrowtype-to-string : erased? → string
vars-to-string : 𝕃 var → strM
bracketL : erased? → string
bracketR : erased? → string
braceL : erased? → string
braceR : erased? → string
opacity-to-string : opacity → string
hole-to-string : posinfo → strM

to-string-ed : {ed : exprd} → ⟦ ed ⟧ → strM
to-string-ed{TERM} = term-to-stringh
to-string-ed{TYPE} = type-to-stringh
to-string-ed{KIND} = kind-to-stringh

to-stringh' : {ed : exprd} → expr-side → ⟦ ed ⟧ → strM
to-stringh' {ed} lr t {ed'} s n ts Γ mp lr' =
  elim-Σi (to-string-rewrite Γ options t) λ t' →
  parens-unless (~ isJust (mp >>= λ pe → maybe-if (~ no-parens t' pe lr)))
    (to-string-ed t') s n ts Γ (just t') lr
  where
  parens-unless : 𝔹 → strM → strM
  parens-unless p s = if p then s else (strAdd "(" >>str strNest 1 s >>str strAdd ")")

to-stringl : {ed : exprd} → ⟦ ed ⟧ → strM
to-stringr : {ed : exprd} → ⟦ ed ⟧ → strM
to-stringl = to-stringh' left
to-stringr = to-stringh' right
to-stringh = to-stringh' neither

set-parent : ∀ {ed} → ⟦ ed ⟧ → strM → strM
set-parent t m s n ts Γ _ lr = m s n ts Γ (just t) lr

apps-to-string : ∀ {ll : 𝔹} → (if ll then term else type) → strM
apps-to-string {tt} t with decompose-apps t
...| tₕ , as = set-parent t $ strList 2
                 (to-stringl tₕ :: map arg-to-string as)
apps-to-string {ff} T with decompose-tpapps T
...| Tₕ , as = set-parent T $ strList 2
                 (to-stringl Tₕ :: map arg-to-string (tmtps-to-args ff as))

lams-to-string : term → strM
lams-to-string t =
  elim-pair (decompose-lams-pretty t) λ xs b →
  set-parent t $ strFold suc filln $ foldr {B = 𝕃 (ℕ × strM)}
    (λ {(x , me , oc) r →
      (0 , (strAdd (lam-to-string me) >>str strAdd " " >>str
            strBvar x (strNest 4 (optClass-to-string oc)) (strAdd " ."))) ::
      map (map-snd $ strΓ' localScope x) r}) [ 2 , to-stringr b ] xs
  where
  decompose-lams-pretty : term → 𝕃 (var × erased? × maybe tpkd) × term
  decompose-lams-pretty = h [] where
    h : 𝕃 (var × erased? × maybe tpkd) → term → 𝕃 (var × erased? × maybe tpkd) × term
    h acc (Lam me x oc t) = h ((x , me , oc) :: acc) t
    h acc t = reverse acc , t

tk-to-stringh (Tkt T) = to-stringh T
tk-to-stringh (Tkk k) = to-stringh k


term-to-stringh (App t t') = apps-to-string (App t t')

term-to-stringh (AppE t tT) = apps-to-string (AppE t tT)

term-to-stringh (Beta t t') = strBreak 3
  0 [ strAdd "β" ]
  2 [ strAdd "<" >>str to-stringh (erase t ) >>str strAdd ">" ]
  2 [ strAdd "{" >>str to-stringh (erase t') >>str strAdd "}" ]

term-to-stringh (Delta T t) = strBreak 3
  0 [ strAdd "δ" ]
  2 [ to-stringl T >>str strAdd " -" ]
  1 [ to-stringr t ]

term-to-stringh (Hole pi) = hole-to-string pi

term-to-stringh (IotaPair t₁ t₂ x Tₓ) = strBreak 3
  1 [ strAdd "[ " >>str to-stringh t₁ >>str strAdd "," ]
  1 [ to-stringh t₂ ]
  1 [ strAdd "@ " >>str
      strBvar x (strAdd " . ") (strNest (5 + string-length x) (to-stringh Tₓ)) >>str
      strAdd " ]" ]

term-to-stringh (IotaProj t n) = to-stringh t >>str strAdd (if n iff ι1 then ".1" else ".2")

term-to-stringh (Lam me x oc t) =  lams-to-string (Lam me x oc t)

term-to-stringh (LetTm me x T t t') = strBreak 4
  1 [ strAdd (bracketL me) >>str strAdd (unqual-local x) ]
  5 ( optType-to-string (just ':') T )
  3 [ strAdd "= " >>str to-stringh t >>str strAdd (bracketR me) ]
  1 [ strΓ' localScope x (to-stringr t') ]

term-to-stringh (LetTp x k T t) = strBreak 4
  1 [ strAdd (bracketL NotErased) >>str strAdd (unqual-local x) ]
  5 [ strAdd ": " >>str to-stringh k ]
  3 [ strAdd "= " >>str to-stringh T >>str strAdd (bracketR NotErased) ]
  1 [ strΓ' localScope x (to-stringr t) ]

term-to-stringh (Phi tₑ t₁ t₂) = strBreak 3
  0 [ strAdd "φ " >>str to-stringl tₑ >>str strAdd " -" ]
  2 [ to-stringh t₁ ]
  2 [ strAdd "{ " >>str to-stringr (erase t₂) >>str strAdd " }" ]

term-to-stringh (Rho tₑ x Tₓ t) = strBreak 3
  0 [ strAdd "ρ " >>str to-stringl tₑ ]
  1 [ strAdd "@ " >>str strBvar x (strAdd " . ") (to-stringh (erase Tₓ)) ]
  1 [ strAdd "- " >>str strNest 2 (to-stringr t) ]

term-to-stringh (Sigma t) = strAdd "ς " >>str to-stringh t

term-to-stringh (Var x) = strVar x

term-to-stringh (Mu (inj₂ x) t ot t~ cs) =
  strAdd "μ " >>str
  strBvar x
    (strAdd " . " >>str strBreak 2
      2 [ to-stringl t ]
      3 ( optType-to-string (just '@') ot ))
    (strAdd " " >>str strBracket '{' (cases-to-string cs) '}')

term-to-stringh (Mu (inj₁ ot) t oT t~ cs) =
  strAdd "μ' " >>str strBreak 3
    2 (maybe-else' {B = 𝕃 strM} ot []
         λ t → [ strAdd "<" >>str to-stringh t >>str strAdd ">" ])
    2 [ to-stringl t ]
    3 ( optType-to-string (just '@') oT ) >>str
  strAdd " " >>str strBracket '{' (cases-to-string cs) '}'


type-to-stringh (TpArrow T a T') = strBreak 2
  2 [ to-stringl T >>str strAdd (arrowtype-to-string a) ]
  2 [ to-stringr T' ]

type-to-stringh (TpAbs me x tk T) = strBreak 2
  3 [ strAdd (binder-to-string me ^ " ") >>str
      strBvar x (strAdd " : " >>str to-stringl -tk' tk >>str strAdd " .") strEmpty ]
  1 [ strΓ' localScope x (to-stringh T) ]

type-to-stringh (TpIota x T₁ T₂) = strBreak 2
  2 [ strAdd "ι " >>str
      strBvar x (strAdd " : " >>str to-stringh T₁ >>str strAdd " .") strEmpty ]
  2 [ strΓ' localScope x (to-stringh T₂) ]

type-to-stringh (TpApp T tT) = apps-to-string (TpApp T tT)

type-to-stringh (TpEq t₁ t₂) = strBreak 2
  2 [ strAdd "{ " >>str to-stringh (erase t₁) ]
  2 [ strAdd "≃ " >>str to-stringh (erase t₂) >>str strAdd " }" ]

type-to-stringh (TpHole pi) = hole-to-string pi

type-to-stringh (TpLam x tk T) = strBreak 2
  3 [ strAdd "λ " >>str
      strBvar x (strAdd " : " >>str tk-to-stringh tk >>str strAdd " .") strEmpty ]
  1 [ strΓ' localScope x (to-stringr T) ]

type-to-stringh (TpVar x) = strVar x


kind-to-stringh (KdArrow k k') = strBreak 2
  2 [ to-stringl -tk' k >>str strAdd " ➔" ]
  2 [ to-stringr k' ]

kind-to-stringh (KdAbs x tk k) = strBreak 2
  4 [ strAdd "Π " >>str
      strBvar x (strAdd " : " >>str to-stringl -tk' tk >>str strAdd " .") strEmpty ]
  1 [ strΓ' localScope x (to-stringh k) ]

kind-to-stringh (KdHole pi) = hole-to-string pi

kind-to-stringh KdStar = strAdd "★"


hole-to-string pi = strM-Γ λ Γ → strAddTags "●" (var-loc-tag Γ (split-var pi) "●")

optTerm-to-string nothing c1 c2 = []
optTerm-to-string (just t) c1 c2 =
  [ strAdd (𝕃char-to-string (c1 :: [ ' ' ])) >>str
    to-stringh t >>str
    strAdd (𝕃char-to-string (' ' :: [ c2 ])) ]

optClass-to-string nothing = strEmpty
optClass-to-string (just atk) = strAdd " : " >>str tk-to-stringh atk

optType-to-string pfx nothing = []
optType-to-string pfx (just T) =
  [ maybe-else strEmpty (λ pfx → strAdd (𝕃char-to-string (pfx :: [ ' ' ]))) pfx >>str to-stringh T ]

arg-to-string (Arg t) = to-stringr t
arg-to-string (ArgE (Ttm t)) = strAdd "-" >>str strNest 1 (to-stringr t)
arg-to-string (ArgE (Ttp T)) = strAdd "·" >>str strNest 2 (to-stringr T)

args-to-string = foldr' strEmpty λ t x → strAdd " " >>str arg-to-string t >>str x

binder-to-string tt = "∀"
binder-to-string ff = "Π"

lam-to-string tt = "Λ"
lam-to-string ff = "λ"

arrowtype-to-string ff = " ➔"
arrowtype-to-string tt = " ➾"

opacity-to-string opacity-open = ""
opacity-to-string opacity-closed = "opaque "

vars-to-string [] = strEmpty
vars-to-string (v :: []) = strVar v
vars-to-string (v :: vs) = strVar v >>str strAdd " " >>str vars-to-string vs

ctr-to-string (Ctr x T) = strAdd x >>str strAdd " : " >>str to-stringh T

case-to-string (Case x as t) =
  strM-Γ λ Γ →
  let as-f = λ x as → strVar x >>str caseArgs-to-string as (strAdd " ➔ " >>str to-stringr t) in
  case (env-lookup Γ x , options) of uncurry λ where
    (just (ctr-def mps T _ _ _ , _ , _)) ced-ops-drop-spine →
          as-f (unqual-all (ctxt-get-qualif Γ) x) as
    _ _ → as-f x as

cases-to-string = h use-newlines where
  h : 𝔹 → cases → strM
  h _ [] = strEmpty
  h tt (m :: []) = strAdd "| " >>str case-to-string m
  h tt (m :: ms) = strAdd "| " >>str case-to-string m >>str strLine >>str h tt ms
  h ff (m :: []) = case-to-string m
  h ff (m :: ms) = case-to-string m >>str strAdd " | " >>str h ff ms

caseArgs-to-string [] m = m
caseArgs-to-string (CaseArg CaseArgTm x :: as) m = strAdd " " >>str strBvar x strEmpty (caseArgs-to-string as m)
caseArgs-to-string (CaseArg CaseArgEr x :: as) m = strAdd " -" >>str strBvar x strEmpty (caseArgs-to-string as m)
caseArgs-to-string (CaseArg CaseArgTp x :: as) m = strAdd " ·" >>str strBvar x strEmpty (caseArgs-to-string as m)

braceL me = if me then "{" else "("
braceR me = if me then "}" else ")"

bracketL me = if me then "{ " else "[ "
bracketR me = if me then " } -" else " ] -"

param-to-string : param → (strM → strM) × strM
param-to-string (Param me v atk) =
  strΓ' localScope v ,
  (strAdd (braceL me) >>str
   strAdd (unqual-local v) >>str
   strAdd " : " >>str
   tk-to-stringh atk >>str
   strAdd (braceR me))

params-to-string'' ps f = elim-pair (foldr (λ p → uncurry λ g ms → elim-pair (param-to-string p) λ h m → g ∘ h , m :: map h ms) (id , []) ps) λ g ms → strList 2 (strEmpty :: ms) >>str g f

params-to-string' f [] = f
params-to-string' f (p :: []) = elim-pair (param-to-string p) λ g m → m >>str g f
params-to-string' f (p :: ps) = elim-pair (param-to-string p) λ g m → m >>str strAdd " " >>str params-to-string' (g f) ps

params-to-string = params-to-string' strEmpty

strRun : ctxt → strM → rope
strRun Γ m = doc-to-rope $ fst $ m {TERM} NIL 0 [] Γ nothing neither

strRunTag : (name : string) → ctxt → strM → tagged-val
strRunTag name Γ m with m {TERM} NIL 0 [] Γ nothing neither
...| s , n , ts = name , doc-to-rope s , ts

to-stringe : {ed : exprd} → ⟦ ed ⟧ → strM
to-stringe = to-stringh ∘' (if cedille-options.options.erase-types options then erase else id)

tpkd-to-stringe : tpkd → strM
tpkd-to-stringe = to-stringe -tk'_

to-string-tag : {ed : exprd} → string → ctxt → ⟦ ed ⟧ → tagged-val
to-string-tag name Γ t = strRunTag name Γ (to-stringe t)

to-string : {ed : exprd} → ctxt → ⟦ ed ⟧ → rope
to-string Γ t = strRun Γ (to-stringh t)


tpkd-to-string : ctxt → tpkd → rope
tpkd-to-string Γ atk = strRun Γ (tpkd-to-stringe atk)

params-to-string-tag : string → ctxt → params → tagged-val
params-to-string-tag name Γ ps = strRunTag name Γ (params-to-string ps)

