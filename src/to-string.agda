import cedille-options

module to-string (options : cedille-options.options) where

open import lib
open import cedille-types
open import constants
open import syntax-util
open import ctxt
open import rename
open import general-util
open import datatype-functions
open import type-util
open import free-vars

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
--is-eq-op{TERM} (Epsilon _ _ _ _) = tt
is-eq-op{TERM} (Rho _ _ _ _) = tt
--is-eq-op{TERM} (Chi _ _ _) = tt
is-eq-op{TERM} (Phi _ _ _) = tt
is-eq-op{TERM} (Delta _ _) = tt
is-eq-op _ = ff

pattern TpArrow tp me tp' = TpAbs me ignored-var (Tkt tp) tp'
pattern KdArrow tk kd = KdAbs ignored-var tk kd

is-arrow : {ed : exprd} → ⟦ ed ⟧ → 𝔹
is-arrow {TYPE} (TpArrow _ _ _) = tt
is-arrow {KIND} (KdArrow _ _) = tt
is-arrow _ = ff

is-type-level-app : ∀ {ed} → ⟦ ed ⟧ → 𝔹
is-type-level-app {TYPE} (TpApp T T') = tt
is-type-level-app {TYPE} (TpAppt T t) = tt
is-type-level-app _ = ff

no-parens : {ed : exprd} → {ed' : exprd} → ⟦ ed ⟧ → ⟦ ed' ⟧ → expr-side → 𝔹
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
no-parens {TERM} {_} (App t me t') p lr = ff
no-parens {TERM} {_} (AppTp t T) p lr = ff
no-parens {TERM} {_} (Beta ot ot') p lr = tt
no-parens {TERM} {_} (Delta T t) p lr = ff
no-parens {TERM} {_} (Hole pi) p lr = tt
no-parens {TERM} {_} (IotaPair t₁ t₂ x Tₓ) p lr = tt
no-parens {TERM} {_} (IotaProj t n) p lr = tt
no-parens {TERM} {_} (Lam me x tk? t) p lr = ff
no-parens {TERM} {_} (LetTm me x T t t') p lr = ff
no-parens {TERM} {_} (LetTp x T t t') p lr = ff
no-parens {TERM} {_} (Open _ _ _) p lr = ff
no-parens {TERM} {_} (Phi tₑ t₁ t₂) p lr = ff
no-parens {TERM} {_} (Rho tₑ x Tₓ t) p lr = ff
no-parens {TERM} {_} (Sigma t) p lr = is-eq-op p
no-parens {TERM} {_} (Var x) p lr = tt
no-parens {TERM} {_} (Mu _ _ _ _ _) p lr = ff
no-parens {TYPE} {e} (TpAbs me x tk T) p lr = exprd-eq e TYPE && is-arrow p && not-left lr
no-parens {TYPE} {_} (TpIota x T₁ T₂) p lr = ff
no-parens {TYPE} {_} (TpApp T T') p lr = is-arrow p || (is-type-level-app p && not-right lr)
no-parens {TYPE} {_} (TpAppt T t) p lr = is-arrow p || (is-type-level-app p && not-right lr)
no-parens {TYPE} {e} (TpArrow T a T') p lr = exprd-eq e TYPE && is-arrow p && not-left lr
no-parens {TYPE} {_} (TpEq t₁ t₂) p lr = tt
no-parens {TYPE} {_} (TpHole pi) p lr = tt
no-parens {TYPE} {_} (TpLam pi pi' x Tk T) p lr = ff
no-parens {TYPE} {_} (TpVar pi x) p lr = tt
no-parens {KIND} {_} (KdArrow k k') p lr = is-arrow p && not-left lr
no-parens {KIND} {_} (KdAbs pi pi' x Tk k) p lr = is-arrow p && not-left lr
no-parens {KIND} {_} (KdStar pi) p lr = tt



pattern ced-ops-drop-spine = cedille-options.options.mk-options _ _ _ _ ff _ _ _ ff _
pattern ced-ops-conv-arr = cedille-options.options.mk-options _ _ _ _ _ _ _ _ ff _
pattern ced-ops-conv-abs = cedille-options.options.mk-options _ _ _ _ _ _ _ _ tt _

drop-spine : cedille-options.options → {ed : exprd} → ctxt → ⟦ ed ⟧ → ⟦ ed ⟧
drop-spine ops @ ced-ops-drop-spine = h
  where
  drop-mod-args : ctxt → erased? → var × args → var × args
  drop-mod-args Γ me (v , as) =
    let qv = unqual-all (ctxt-get-qualif Γ) v in qv ,
    maybe-else' (maybe-if (~ v =string qv) ≫maybe ctxt-qualif-args-length Γ me qv)
      as (λ n → reverse (drop n (reverse as)))

  h : {ed : exprd} → ctxt → ⟦ ed ⟧ → ⟦ ed ⟧
  h {TERM} Γ t with decompose-apps t
  ...| Var _ x , as = uncurry (flip recompose-apps) $ map-fst (Var posinfo-gen) $ drop-mod-args Γ ff (x , as)
  ...| _ = t
  h {TYPE} Γ T with decompose-tpapps T
  ...| TpVar _ x , as = uncurry (flip recompose-tpapps) $ map-fst (TpVar posinfo-gen) $ map-snd (map λ {(TmArg me t) → inj₁ t; (TpArg T) → inj₂ T}) $ drop-mod-args Γ ff (x , map (λ e → either-else' e (TmArg ff) TpArg) as)
  ...| _ = T
  h Γ x = x
drop-spine ops Γ x = x

to-string-rewrite : {ed : exprd} → ctxt → cedille-options.options → ⟦ ed ⟧ → Σi exprd ⟦_⟧'
--to-string-rewrite{TERM} Γ ops (Parens _ t _) = to-string-rewrite Γ ops t
--to-string-rewrite{TYPE} Γ ops (TpParens _ T _) = to-string-rewrite Γ ops T
--to-string-rewrite{KIND} Γ ops (KdParens _ k _) = to-string-rewrite Γ ops k
to-string-rewrite{TYPE} Γ ced-ops-conv-arr (TpAbs _ me _ ignored-var (Tkt T) T') = , TpArrow T me T'
to-string-rewrite{KIND} Γ ced-ops-conv-arr (KdAbs _ _ ignored-var atk k) = , KdArrow atk k
to-string-rewrite{TYPE} Γ ced-ops-conv-abs (TpArrow T me T') = , TpAbs posinfo-gen me posinfo-gen ignored-var (Tkt T) T'
to-string-rewrite{KIND} Γ ced-ops-conv-abs (KdArrow k k') = , KdAbs posinfo-gen posinfo-gen ignored-var k k'
--to-string-rewrite{LIFTINGTYPE} Γ ced-ops-conv-abs (LiftTpArrow T lT) = , LiftPi posinfo-gen ignored-var T lT
to-string-rewrite{TERM} Γ ops @ ced-ops-conv-abs (Open _ _ _ _ t) = to-string-rewrite Γ ops t
to-string-rewrite{TERM} Γ ops (Sigma pi t) with to-string-rewrite Γ ops t
...| ,_ {TERM} (Sigma pi' t') = , t'
...| ,_ {TERM} t' = , Sigma posinfo-gen t'
...| t? = , Sigma posinfo-gen t
--to-string-rewrite{TERM} Γ ops (Phi pi eq t u pi') = , Phi pi eq t (erase u) pi'
--to-string-rewrite{TERM} Γ ops (Rho pi op on eq og t) = , Rho pi op on eq (flip maybe-map og λ _ → erase) t
--to-string-rewrite{TERM} Γ ops (Beta pi ot ot') = , Beta pi (maybe-map erase ot) (maybe-map erase ot')
--to-string-rewrite{TERM} Γ ops (Chi _ nothing t@(Var _ _)) = to-string-rewrite Γ ops t
--to-string-rewrite{TYPE} Γ ops (TpEq pi t₁ t₂ pi') = , TpEq pi (erase t₁) (erase t₂) pi'
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

private to-stringh : {ed : exprd} → ⟦ ed ⟧ → strM

strM-Γ : (ctxt → strM) → strM
strM-Γ f s n ts Γ = f Γ s n ts Γ

infixr 4 _≫str_

_≫str_ : strM → strM → strM
(m ≫str m') s n ts Γ pe lr with m s n ts Γ pe lr
(m ≫str m') s n ts Γ pe lr | s' , n' , ts' = m' s' n' ts' Γ pe lr

strAdd : string → strM
strAdd s s' n ts Γ pe lr = s' <> TEXT [[ s ]] , n + string-length s , ts

--strFlatten : strM → strM
--strFlatten m s n ts Γ pe lr with m nil n ts Γ pe lr
--...| s' , n' , ts' = s <> flatten s' , n' , ts'

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

strList : ℕ → 𝕃 strM → strM
strList i = strFoldi i suc λ ms → flatten (spread ms) :<|> stack ms
-- strNest i ∘' strFold suc (λ ms → let ms = map snd ms in flatten (spread ms) :<|> stack ms) ∘' map (_,_ 0)

strBreak' : 𝕃 (ℕ × strM) → strM
strBreak' = strFold suc filln

-- i = indent, n = number of strM args
strBreak : (n : ℕ) → fold n strM λ X → ℕ → strM → X
strBreak = h [] where
  h : 𝕃 (ℕ × strM) → (n : ℕ) → fold n strM λ X → ℕ → strM → X
  h ms (suc n) i m = h ((i , m) :: ms) n
  h ms zero = strBreak' $ reverse ms


strBracket : char → char → strM → strM
strBracket l r m s n ts Γ pe lr with m nil (suc (suc n)) ts Γ pe lr
...| s' , n' , ts' = s <> bracket (char-to-string l) s' (char-to-string r) , suc (suc n') , ts'

strΓ' : defScope → var → strM → strM
strΓ' ds v m s n ts Γ@(mk-ctxt (fn , mn , ps , q) syms i symb-occs Δ) pe =
  let gl = ds iff globalScope
      v' = if gl then (mn # v) else v in
  m s n ts (mk-ctxt
      (fn , mn , ps , qualif-insert-params q v' (unqual-local v) (if gl then ps else []))
      syms (trie-insert i v' (var-decl , ("missing" , "missing"))) symb-occs Δ) pe

strΓ : var → strM → strM
strΓ x m s n ts Γ = m s n ts (ctxt-var-decl x Γ)

ctxt-get-file-id : ctxt → (filename : string) → ℕ
ctxt-get-file-id (mk-ctxt mod (syms , mn-fn , mn-ps , ids , id) is os Δ) =
  trie-lookup-else 0 ids

make-loc-tag : ctxt → (filename start-to end-to : string) → (start-from end-from : ℕ) → tag
make-loc-tag Γ fn s e = make-tag "loc"
  (("fn" , [[ ℕ-to-string (ctxt-get-file-id Γ fn) ]]) ::
   ("s" , [[ s ]]) :: ("e" , [[ e ]]) :: [])

var-loc-tag : ctxt → location → var → 𝕃 (string × 𝕃 tag)
var-loc-tag Γ ("missing" , "missing") x = []
var-loc-tag Γ ("" , _) x = []
var-loc-tag Γ (_ , "") x = []
var-loc-tag Γ (fn , pi) x =
  let fn-tag = "fn" , [[ ℕ-to-string (ctxt-get-file-id Γ fn) ]]
      s-tag = "s" , [[ pi ]]
      e-tag = "e" , [[ posinfo-plus-str pi x ]] in
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
strBvar v cm bm = strAdd (unqual-local v) ≫str cm ≫str strΓ' localScope v bm

strMetaVar : var → span-location → strM
strMetaVar x (fn , pi , pi') s n ts Γ pe lr =
  let n' = n + string-length x in
  s <> TEXT [[ x ]] , n' , make-loc-tag Γ fn pi pi' n n' :: ts


{-# TERMINATING #-}
term-to-stringh : term → strM
type-to-stringh : type → strM
kind-to-stringh : kind → strM
--liftingType-to-stringh : liftingType → strM
tk-to-stringh : tpkd → strM
ctr-to-string : ctr → strM
--ctrs-to-string : ctrs → strM
case-to-string : case → strM
cases-to-string : cases → strM
caseArgs-to-string : case-args → strM → strM
let-to-string : erased? → def → strM → strM

params-to-string : params → strM
params-to-string' : strM → params → strM
params-to-string'' : params → strM → strM
file-to-string : file → strM
cmds-to-string : cmds → strM → strM
cmd-to-string : cmd → strM → strM  
optTerm-to-string : maybe term → string → string → 𝕃 (ℕ × strM)
optClass-to-string : maybe tpkd → strM
--optGuide-to-string : maybe  → 𝕃 (ℕ × strM)
--optNums-to-string : maybe (𝕃 num) → strM
optType-to-string : ℕ → maybe char → maybe type → 𝕃 (ℕ × strM)
lterms-to-string : 𝕃 lterm → strM
arg-to-string : arg → strM
args-to-string : args → strM
binder-to-string : erased? → string
opacity-to-string : opacity → string
maybeErased-to-string : erased? → string
lam-to-string : erased? → string
leftRight-to-string : left-right → string
vars-to-string : 𝕃 var → strM
nums-to-string : 𝕃 num → strM
theta-to-string : theta → strM
arrowtype-to-string : erased? → string
maybeMinus-to-string : maybeMinus → string
optPlus-to-string : rho-hnf → string
optPublic-to-string : 𝔹 → string
optAs-to-string : maybe import-as → strM
bracketL : erased? → string
bracketR : erased? → string
braceL : erased? → string
braceR : erased? → string

to-string-ed : {ed : exprd} → ⟦ ed ⟧ → strM
to-string-ed{TERM} = term-to-stringh
to-string-ed{TYPE} = type-to-stringh
to-string-ed{KIND} = kind-to-stringh

to-stringh' : {ed : exprd} → expr-side → ⟦ ed ⟧ → strM
to-stringh' {ed} lr t {ed'} s n ts Γ mp lr' =
  elim-Σi (to-string-rewrite Γ options t) λ t' →
  parens-unless (~ isJust (mp ≫=maybe λ pe → maybe-if (~ no-parens t' pe lr)))
    (to-string-ed t') s n ts Γ (just t') lr
  where
  parens-unless : 𝔹 → strM → strM
  parens-unless p s = if p then s else (strAdd "(" ≫str strNest 1 s ≫str strAdd ")")

to-stringl : {ed : exprd} → ⟦ ed ⟧ → strM
to-stringr : {ed : exprd} → ⟦ ed ⟧ → strM
to-stringl = to-stringh' left
to-stringr = to-stringh' right
to-stringh = to-stringh' neither

--to-string-tk : ({ed : exprd} → ⟦ ed ⟧ → strM) → tk → strM
--to-string-tk f (Tkt T) = f T
--to-string-tk f (Tkk k) = f k

set-parent : ∀ {ed} → ⟦ ed ⟧ → strM → strM
set-parent t m s n ts Γ _ lr = m s n ts Γ (just t) lr

apps-to-string : ∀ {ll : 𝔹} → (if ll then term else type) → strM
apps-to-string {tt} t with decompose-apps t
...| tₕ , as = set-parent t $ strList 2 $ (to-stringl tₕ :: map arg-to-string as)
apps-to-string {ff} T with decompose-tpapps T
...| Tₕ , as = set-parent T $ strList 2 $ (to-stringl Tₕ :: map (arg-to-string ∘ λ e → either-else' e (TmArg ff) TpArg) as)

lams-to-string : term → strM
lams-to-string t =
  elim-pair (decompose-lams-pretty t) λ xs b →
  set-parent t $ strBreak' $ foldr {B = 𝕃 (ℕ × strM)}
    (λ {(x , me , oc) r →
      (0 , strAdd (lam-to-string me) ≫str strAdd " " ≫str
        strBvar x (strNest 4 (optClass-to-string oc)) (strAdd " .")) ::
      map (map-snd $ strΓ' localScope x) r}) [ 2 , to-stringr b ] xs
  where
  decompose-lams-pretty : term → 𝕃 (var × erased? × maybe tpkd) × term
  decompose-lams-pretty = h [] where
    h : 𝕃 (var × erased? × maybe tpkd) → term → 𝕃 (var × erased? × maybe tpkd) × term
    h acc (Lam _ me _ x oc t) = h ((x , me , oc) :: acc) t
    h acc t = reverse acc , t

tk-to-stringh (Tkt T) = to-stringh T
tk-to-stringh (Tkk k) = to-stringh k

term-to-stringh (App t me t') = apps-to-string (App t me t')
term-to-stringh (AppTp t T) = apps-to-string (AppTp t T)
term-to-stringh (Beta pi ot ot') = strBreak' ((0 , strAdd "β") :: optTerm-to-string (maybe-map pos-tm-to-tm ot) "< " " >" ++ optTerm-to-string (maybe-map pos-tm-to-tm ot') "{ " " }") -- strBreak 3 0 (strAdd "β") 2 (optTerm-to-string ot "< " " >") 2 (optTerm-to-string ot' "{ " " }")}
--term-to-stringh (Chi pi mT t) = strBreak' ((0 , strAdd "χ") :: (optType-to-string 2 nothing mT) ++ (2 , strAdd "-") :: [ 2 , to-stringr t ])
term-to-stringh (Delta pi mT t) = strBreak' ((0 , strAdd "δ") :: (optType-to-string 2 nothing mT) ++ (2 , strAdd "-") :: [ 2 , to-stringr t ])
--term-to-stringh (Epsilon pi lr m t) = strAdd "ε" ≫str strAdd (leftRight-to-string lr) ≫str strAdd (maybeMinus-to-string m) ≫str to-stringh t
term-to-stringh (Hole pi) = strM-Γ λ Γ → strAddTags "●" (var-loc-tag Γ (split-var pi) "●")
term-to-stringh (IotaPair t₁ t₂ x Tₓ) = strBreak' ((1 , strAdd "[ " ≫str to-stringh t₁ ≫str strAdd ",") :: (1 , to-stringh t₂) :: [ 1 , strAdd "@ " ≫str strBvar x (strAdd " . ") (to-stringh Tₓ) ]) ≫str strAdd " ]"
term-to-stringh (IotaProj t n pi) = to-stringh t ≫str strAdd ("." ^ n)
term-to-stringh (Lam pi l pi' x oc t) = lams-to-string (Lam pi l pi' x oc t)
term-to-stringh (LetTm me x T t t') = strBreak 2 0 ? 1 ?
term-to-stringh (Open pi o pi' x t) = strBreak 2 0 (strAdd (if o then "open " else "close ") ≫str strVar x ≫str strAdd " -") 2 (to-stringh t)
--term-to-stringh (Parens pi t pi') = to-stringh t
term-to-stringh (Phi pi eq t t' pi') = strBreak 3 0 (strAdd "φ " ≫str to-stringl eq ≫str strAdd " -") 2 (to-stringh t) 2 (strAdd "{ " ≫str to-stringr t' ≫str strAdd " }")
term-to-stringh (Rho tₑ x Tₓ t) = strBreak' ((0 , strAdd "ρ" ≫str to-stringl tₑ) :: (1 , strAdd "@ " ≫str strBvar x (strAdd " . ") (to-stringh Tₓ)) :: [ 1 , strAdd "- " ≫str strNest 2 (to-stringr t) ])
term-to-stringh (Sigma pi t) = strAdd "ς " ≫str to-stringh t
--term-to-stringh (Theta pi theta t lts) = theta-to-string theta ≫str to-stringh t ≫str lterms-to-string lts
term-to-stringh (Var pi x) = strVar x
term-to-stringh (Mu pi (inj₂ x) t ot pi'' cs pi''') = strAdd "μ " ≫str strBvar x (strAdd " . " ≫str strBreak' ((2 , to-stringl t) :: (optType-to-string 3 (just '@') ot))) (strAdd " " ≫str strBracket '{' '}' (cases-to-string cs))
term-to-stringh (Mu pi (inj₁ ot) t oT pi' cs pi'') = strAdd "μ' " ≫str strBreak' ((optTerm-to-string ot " < " " > ") ++ (2 , to-stringl t) :: (optType-to-string 3 (just '@') oT)) ≫str strAdd " " ≫str strBracket '{' '}' (cases-to-string cs)

type-to-stringh (TpAbs pi b pi' x tk T) = strBreak 2 3 (strAdd (binder-to-string b ^ " ") ≫str strBvar x (strAdd " : " ≫str to-stringl -tkx tk ≫str strAdd " .") strEmpty) 1 (strΓ' localScope x (to-stringh T))
type-to-stringh (TpIota pi pi' x T T') = strBreak 2 2 (strAdd "ι " ≫str strBvar x (strAdd " : " ≫str to-stringh T ≫str strAdd " .") strEmpty) 2 (strΓ' localScope x (to-stringh T'))
--type-to-stringh (Lft pi pi' x t lT) = strAdd "↑ " ≫str strBvar x (strAdd " . ") (to-stringh t) ≫str strAdd " : " ≫str to-stringh lT
--type-to-stringh (TpNoSpans T pi) = to-string-ed T
type-to-stringh (TpApp T T') = apps-to-string (TpApp T T')
type-to-stringh (TpAppt T t) = apps-to-string (TpAppt T t)
--type-to-stringh (TpArrow T a T') = strBreak 2 2 (to-stringl T ≫str strAdd (arrowtype-to-string a)) 2 (to-stringr T')
type-to-stringh (TpEq _ t t' _) = strAdd "{ " ≫str to-stringh t ≫str strAdd " ≃ " ≫str to-stringh t' ≫str strAdd " }"
type-to-stringh (TpHole pi) = strM-Γ λ Γ → strAddTags "●" (var-loc-tag Γ (split-var pi) "●")
type-to-stringh (TpLam pi pi' x Tk T) = strBreak 2 3 (strAdd "λ " ≫str strBvar x (strAdd " : " ≫str tk-to-stringh Tk ≫str strAdd " .") strEmpty) 1 (strΓ' localScope x (to-stringr T))
--type-to-stringh (TpParens pi T pi') = to-stringh T
type-to-stringh (TpVar pi x) = strVar x
--type-to-stringh (TpLet pi dtT T) = let-to-string NotErased dtT (to-stringh T)

--kind-to-stringh (KdArrow k k') = strBreak 2 2 (to-stringl -tkx k ≫str strAdd " ➔") 2 (to-stringr k')
--kind-to-stringh (KdParens pi k pi') = to-stringh k
kind-to-stringh (KdAbs pi pi' x tk k) = strBreak 2 4 (strAdd "Π " ≫str strBvar x (strAdd " : " ≫str to-stringl -tkx tk ≫str strAdd " .") strEmpty) 1 (strΓ' localScope x (to-stringh k))
--kind-to-stringh (KndTpArrow T k) = strBreak 2 2 (to-stringl T ≫str strAdd " ➔") 2 (to-stringr k)
--kind-to-stringh (KdVar pi x as) = strList 2 (strKvar x :: map arg-to-string as)
kind-to-stringh (KdStar pi) = strAdd "★"

{-
liftingType-to-stringh (LiftArrow lT lT') = to-stringl lT ≫str strAdd " ➔↑ " ≫str to-stringr lT'
liftingType-to-stringh (LiftParens pi lT pi') = strAdd "(" ≫str to-string-ed lT ≫str strAdd ")"
liftingType-to-stringh (LiftPi pi x T lT) = strAdd "Π↑ " ≫str strBvar x (strAdd " : " ≫str to-stringh T ≫str strAdd " . ") (to-stringh lT)
liftingType-to-stringh (LiftStar pi) = strAdd "☆"
liftingType-to-stringh (LiftTpArrow T lT) = to-stringl T ≫str strAdd " ➔↑ " ≫str to-stringr lT
-}

optTerm-to-string nothing c1 c2 = []
optTerm-to-string (just t) c1 c2 = [ string-length c1 , strAdd c1 ≫str to-stringh t  ≫str strAdd c2 ]
optClass-to-string nothing = strEmpty
optClass-to-string (just atk) = strAdd " : " ≫str tk-to-stringh atk
--optGuide-to-string nothing = []
--optGuide-to-string (just (Guide pi v T)) = [ 2 , strAdd "@ " ≫str strBvar v (strAdd " . ") (to-stringh T) ]
optType-to-string i pfx nothing = []
optType-to-string i pfx (just T) = [ i , maybe-else strEmpty (λ pfx → strAdd (𝕃char-to-string (pfx :: [ ' ' ]))) pfx ≫str to-stringh T ]
lterms-to-string (Lterm m t :: ts) = strAdd (" " ^ maybeErased-to-string m) ≫str to-stringh t ≫str lterms-to-string ts
lterms-to-string [] = strEmpty
arg-to-string (TmArg tt t) = strAdd "-" ≫str strNest 1 (to-stringh t)
arg-to-string (TmArg ff t) = to-stringh t
arg-to-string (TpArg T) = strAdd "·" ≫str strNest 2 (to-stringh T)
args-to-string = foldr' strEmpty λ t x → strAdd " " ≫str arg-to-string t ≫str x
binder-to-string tt = "∀"
binder-to-string ff = "Π"
opacity-to-string ff = "opaque "
opacity-to-string tt = ""
maybeErased-to-string tt = "-"
maybeErased-to-string ff = ""
lam-to-string tt = "Λ"
lam-to-string ff = "λ"
leftRight-to-string (just ff) = "l"
leftRight-to-string (just tt) = "r"
leftRight-to-string nothing = ""
vars-to-string [] = strEmpty
vars-to-string (v :: []) = strVar v
vars-to-string (v :: vs) = strVar v ≫str strAdd " " ≫str vars-to-string vs
theta-to-string Abstract = strAdd "θ "
theta-to-string AbstractEq = strAdd "θ+ "
theta-to-string (AbstractVars vs) = strAdd "θ<" ≫str vars-to-string vs ≫str strAdd "> "
nums-to-string [] = strEmpty
nums-to-string (n :: []) = strAdd n
nums-to-string (n :: ns) = strAdd n ≫str strAdd " " ≫str nums-to-string ns
--optNums-to-string nothing = strEmpty
--optNums-to-string (just ns) = strAdd "<" ≫str nums-to-string ns ≫str strAdd ">"
arrowtype-to-string ff = " ➔"
arrowtype-to-string tt = " ➾"
maybeMinus-to-string ff = ""
maybeMinus-to-string tt = "-"
optPlus-to-string ff = ""
optPlus-to-string tt = "+"
optPublic-to-string ff = ""
optPublic-to-string tt = "public "
optAs-to-string nothing = strEmpty
optAs-to-string (just (ImportAs _ x)) = strAdd " as " ≫str strAdd x
ctr-to-string (Ctr _ x T) = strAdd x ≫str strAdd " : " ≫str to-stringh T
case-to-string (Case _ x as t) =
  strM-Γ λ Γ →
  let as-f = λ x as → strVar x ≫str caseArgs-to-string as (strAdd " ➔ " ≫str to-stringr t) in
  case (env-lookup Γ x , options) of uncurry λ where
    (just (ctr-def mps T _ _ _ , _ , _)) ced-ops-drop-spine →
          as-f (unqual-all (ctxt-get-qualif Γ) x) as
    _ _ → as-f x as

cases-to-string = h use-newlines where
  h : 𝔹 → ex-cases → strM
  h _ [] = strEmpty
  h tt (m :: []) = strAdd "| " ≫str case-to-string m
  h tt (m :: ms) = strAdd "| " ≫str case-to-string m ≫str strLine ≫str h tt ms
  h ff (m :: []) = case-to-string m
  h ff (m :: ms) = case-to-string m ≫str strAdd " | " ≫str h ff ms

caseArgs-to-string [] m = m
caseArgs-to-string (CaseArg CaseArgTm pi x :: as) m = strAdd " " ≫str strBvar x strEmpty (caseArgs-to-string as m)
caseArgs-to-string (CaseArg CaseArgEr pi x :: as) m = strAdd " -" ≫str strBvar x strEmpty (caseArgs-to-string as m)
caseArgs-to-string (CaseArg CaseArgTp pi x :: as) m = strAdd " ·" ≫str strBvar x strEmpty (caseArgs-to-string as m)

let-to-string fe (DefTerm _ x m t') t = strBreak' $
  (1 , strAdd (bracketL fe) ≫str strAdd (unqual-local x)) ::
  (optType-to-string 5 (just ':') m) ++
  (3 , strAdd "= " ≫str to-stringh t' ≫str strAdd (bracketR fe)) ::
  [ 1 , strΓ' localScope x t ]
let-to-string _ (DefType _ x k T) t = strBreak 4
  1 (strAdd (bracketL NotErased) ≫str strAdd (unqual-local x))
  5 (strAdd ": " ≫str to-stringh k)
  3 (strAdd "= " ≫str to-stringh T ≫str strAdd (bracketR NotErased))
  1 (strΓ' localScope x t)

braceL me = if me then "{" else "("
braceR me = if me then "}" else ")"
bracketL me = if me then "{ " else "[ "
bracketR me = if me then " } -" else " ] -"

param-to-string : ex-param → (strM → strM) × strM
param-to-string (Param pi me pi' v atk _) =
  strΓ' localScope v ,
  strAdd (braceL me) ≫str
  strAdd (unqual-local v) ≫str
  strAdd " : " ≫str
  tk-to-stringh atk ≫str
  strAdd (braceR me)

params-to-string'' ps f = elim-pair (foldr (λ p → uncurry λ g ms → elim-pair (param-to-string p) λ h m → g ∘ h , m :: map h ms) (id , []) ps) λ g ms → strList 2 (strEmpty :: ms) ≫str g f


params-to-string' f [] = f
params-to-string' f (p :: []) = elim-pair (param-to-string p) λ g m → m ≫str g f
params-to-string' f (p :: ps) = elim-pair (param-to-string p) λ g m → m ≫str strAdd " " ≫str params-to-string' (g f) ps

params-to-string = params-to-string' strEmpty

file-to-string (Module is _ _ mn ps cs _) =
   cmds-to-string (imps-to-cmds is)
  (strAdd "module " ≫str
   strAdd mn ≫str
   params-to-string'' ps
    (strAdd "." ≫str strLine ≫str
     cmds-to-string cs strEmpty))

cmds-to-string [] f = f
cmds-to-string (c :: cs) f =
  let nl = if use-newlines then "" else "\n" in
  strLine ≫str
  strAdd nl ≫str
  cmd-to-string c
  (strLine ≫str
   strAdd nl ≫str
   cmds-to-string cs f)
  
cmd-to-string (CmdDef op (DefTerm pi x nothing t) _) f =
  strM-Γ λ Γ →
  let ps = ctxt-get-current-params Γ
      ps' = if pi =string elab-hide-key then params-set-erased Erased ps else ps in
  strBreak'
    ( (0 , strAdd (opacity-to-string op) ≫str strAdd x ≫str strAdd " =") ::
     [ 2 , to-stringh t ≫str strAdd " ." ]) ≫str
  strΓ' globalScope x f
cmd-to-string (CmdDef op (DefTerm pi x (just T) t) _) f =
  strM-Γ λ Γ →
  let ps = ctxt-get-current-params Γ
      ps' = if pi =string elab-hide-key then params-set-erased Erased ps else ps in
  strBreak'
    (( 2 , strAdd (opacity-to-string op) ≫str strAdd x ≫str strAdd " :" ) ::
     ( 4 , to-stringh T ≫str strAdd " =" ) ::
     [ 2 , to-stringh t ≫str strAdd " ." ]) ≫str
  strΓ' globalScope x f
cmd-to-string (CmdDef op (DefType pi x k T) _) f =
  strM-Γ λ Γ →
  let ps = ctxt-get-current-params Γ
      ps' = if pi =string elab-hide-key then params-set-erased Erased ps else ps in
  strBreak'
    (( 2 , strAdd (opacity-to-string op) ≫str strAdd x ≫str strAdd " :" ) ::
     ( 4 , to-stringh k ≫str strAdd " =" ) ::
     [ 2 , to-stringh T ≫str strAdd " ." ]) ≫str
  strΓ' globalScope x f
cmd-to-string (CmdKind pi x ps k _) f =
  strM-Γ λ Γ →
  strAdd x ≫str
  params-to-string'' ps
  (strAdd " = " ≫str
   to-stringh k ≫str
   strAdd " .") ≫str
  strΓ' globalScope x f
cmd-to-string (CmdImport (Import _ op _ fn oa as _)) f =
  let m = strAdd "import " ≫str
          strAdd (optPublic-to-string op) ≫str
          strAdd fn ≫str
          optAs-to-string oa in
  strList 2 (m :: map arg-to-string as) ≫str
  strAdd " ." ≫str
  f
cmd-to-string (CmdData (DefDatatype pi pi' x ps k cs) pi'') f =
  strAdd "data " ≫str
  strAdd x ≫str  
  params-to-string'' ps
   (strBreak 2 0 (strAdd " :") 4 (kind-to-stringh k ≫str strAdd " =") ≫str
    strNest 2 (foldr {B = strM}
      (λ c m → strLine ≫str strAdd "| " ≫str strNest 2 (ctr-to-string c) ≫str m)
      strEmpty cs) ≫str
    strAdd " .") ≫str
  strΓ' globalScope x f

strRun : ctxt → strM → rope
strRun Γ m = doc-to-rope $ fst $ m {TERM} NIL 0 [] Γ nothing neither

strRunTag : (name : string) → ctxt → strM → tagged-val
strRunTag name Γ m with m {TERM} NIL 0 [] Γ nothing neither
...| s , n , ts = name , doc-to-rope s , ts


{-
{-# TERMINATING #-}
resugar : ∀ {ed} → ⟦ ed ⟧ → ⟦ ed ⟧
resugar-tk : tpkd → ex-tk

resugar {TERM} (App t me t') = App (resugar t) me (resugar t')
resugar {TERM} (AppTp t T) = AppTp (resugar t) (resugar T)
resugar {TERM} (Beta ot ot') = Beta pi-gen (maybe-map (λ t → PosTm (resugar t) pi-gen) ot) (maybe-map (λ t → PosTm (resugar t) pi-gen) ot)
resugar {TERM} (Delta T t) = Delta pi-gen (just (resugar T)) (resugar t)
resugar {TERM} (Hole pi) = Hole pi
resugar {TERM} (IotaPair t₁ t₂ x Tₓ) = IotaPair pi-gen (resugar t₁) (resugar t₂) (just (Guide pi-gen x (resugar Tₓ))) pi-gen
resugar {TERM} (IotaProj t n) = IotaProj (resugar t) (if n then "2" else "1") pi-gen
resugar {TERM} (Lam me x atk t) = Lam pi-gen me pi-gen x (maybe-map resugar-tk atk) (resugar t)
resugar {TERM} (LetTm me x T? t t') = Let pi-gen me (DefTerm pi-gen x (maybe-map resugar T?) (resugar t)) (resugar t')
resugar {TERM} (LetTp x k T t) = Let pi-gen tt (DefType pi-gen x (resugar k) (resugar T)) (resugar t)
resugar {TERM} (Open op x t) = Open pi-gen op pi-gen x (resugar t)
resugar {TERM} (Phi tₑ t₁ t₂) = Phi pi-gen (resugar tₑ) (resugar t₁) (resugar t₂) pi-gen
resugar {TERM} (Rho tₑ x Tₓ t) = Rho pi-gen ff nothing (resugar tₑ) (just (Guide pi-gen x (resugar Tₓ))) (resugar t)
resugar {TERM} (Sigma t) = Sigma pi-gen (resugar t)
resugar {TERM} (Mu μ t Tₘ t~ cs) = t~ (either-else' μ (IsMu' ∘ maybe-map resugar) (IsMu pi-gen)) (resugar t) (maybe-map resugar Tₘ) (map (λ {(Case x cas t) → Case pi-gen x (map (λ {(CaseArg e x) → CaseArg e pi-gen x}) cas) (resugar t)}) cs)
resugar {TERM} (Var x) = Var pi-gen x
resugar {TYPE} (TpAbs me x (Tkt T) T') = if is-free-in x T' then TpAbs pi-gen me pi-gen x (Tkt (resugar T)) (resugar T') else TpArrow (resugar T) me (resugar T')
resugar {TYPE} (TpAbs me x (Tkk k) T) = TpAbs pi-gen me pi-gen x (Tkk (resugar k)) (resugar T)
resugar {TYPE} (TpIota x T₁ T₂) = TpIota pi-gen pi-gen x (resugar T₁) (resugar T₂)
resugar {TYPE} (TpApp T T') = TpApp (resugar T) (resugar T')
resugar {TYPE} (TpAppt T t) = TpAppt (resugar T) (resugar t)
resugar {TYPE} (TpEq t₁ t₂) = TpEq pi-gen (resugar t₁) (resugar t₂) pi-gen
resugar {TYPE} (TpHole pi) = TpHole pi
resugar {TYPE} (TpLam x tk T) = TpLam pi-gen pi-gen x (resugar-tk tk) (resugar T)
resugar {TYPE} (TpVar x) = TpVar pi-gen x
resugar {KIND} KdStar = KdStar pi-gen
resugar {KIND} (KdAbs x tk k) = if is-free-in x k then KdAbs pi-gen pi-gen x (resugar-tk tk) (resugar k) else KdArrow (resugar-tk tk) (resugar k)

resugar-tk (Tkt T) = Tkt (resugar T)
resugar-tk (Tkk k) = Tkk (resugar k)

resugar-params : params → ex-params
resugar-params ps = ?
-}

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

