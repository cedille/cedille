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
exprd-eq TPKD TPKD = tt
exprd-eq _ _ = ff

is-eq-op : {ed : exprd} → ⟦ ed ⟧' → 𝔹
is-eq-op{TERM} (ExSigma _ _) = tt
is-eq-op{TERM} (ExEpsilon _ _ _ _) = tt
is-eq-op{TERM} (ExRho _ _ _ _ _ _) = tt
is-eq-op{TERM} (ExChi _ _ _) = tt
is-eq-op{TERM} (ExPhi _ _ _ _ _) = tt
is-eq-op{TERM} (ExDelta _ _ _) = tt
is-eq-op _ = ff

is-arrow : {ed : exprd} → ⟦ ed ⟧' → 𝔹
is-arrow {TYPE} (ExTpArrow _ _ _) = tt
is-arrow {KIND} (ExKdArrow _ _) = tt
is-arrow _ = ff

no-parens : {ed : exprd} → {ed' : exprd} → ⟦ ed ⟧' → ⟦ ed' ⟧' → expr-side → 𝔹
no-parens {_} {TERM} _ (ExIotaPair pi t t' og pi') lr = tt
no-parens {_} {TYPE} _ (ExTpEq _ t t' _) lr = tt
no-parens {_} {TERM} _ (ExBeta pi ot ot') lr = tt
no-parens {_} {TERM} _ (ExPhi pi eq t t' pi') right = tt
no-parens {_} {TERM} _ (ExPhi pi eq t t' pi') neither = tt
no-parens {_} {TERM} _ (ExRho _ _ _ _ _ _) right = tt
no-parens {_} {TERM} _ (ExChi _ _ _) right = tt
no-parens {_} {TERM} _ (ExDelta _ _ _) right = tt
no-parens {_} {TERM} _ (ExLet _ _ _ _) lr = tt
no-parens {_} {TERM} _ (ExLam _ _ _ _ _ _) lr = tt
no-parens {_} {TERM} _ (ExMu _ _ _ _ _ _ _) right = tt
no-parens {_} {TYPE} _ (ExTpLam _ _ _ _ _) lr = tt
no-parens {_} {TYPE} _ (ExTpAbs _ _ _ _ _ _) lr = tt
no-parens {_} {KIND} _ (ExKdAbs _ _ _ _ _) neither = tt
no-parens {_} {TYPE} _ (ExTpIota _ _ _ _ _) lr = tt
no-parens {TERM} {_} (ExApp t me t') p lr = ff --is-term-level-app p && not-right lr
no-parens {TERM} {_} (ExAppTp t T) p lr = ff --is-term-level-app p && not-right lr
no-parens {TERM} {_} (ExBeta pi ot ot') p lr = tt
no-parens {TERM} {_} (ExChi pi mT t) p lr = ff
no-parens {TERM} {_} (ExDelta pi mT t) p lr = ff
no-parens {TERM} {_} (ExEpsilon pi lr' m t) p lr = is-eq-op p
no-parens {TERM} {_} (ExHole pi) p lr = tt
no-parens {TERM} {_} (ExIotaPair pi t t' og pi') p lr = tt
no-parens {TERM} {_} (ExIotaProj t n pi) p lr = tt
no-parens {TERM} {_} (ExLam pi l' pi' x oc t) p lr = ff
no-parens {TERM} {_} (ExLet pi _ dtT t) p lr = ff
no-parens {TERM} {_} (ExOpen _ _ _ _ _) p lr = ff
no-parens {TERM} {_} (ExParens pi t pi') p lr = tt
no-parens {TERM} {_} (ExPhi pi eq t t' pi') p lr = ff
no-parens {TERM} {_} (ExRho pi op on eq og t) p lr = ff
no-parens {TERM} {_} (ExSigma pi t) p lr = is-eq-op p
no-parens {TERM} {_} (ExTheta pi theta t lts) p lr = ff
no-parens {TERM} {_} (ExVar pi x) p lr = tt
no-parens {TERM} {_} (ExMu _ _ _ _ _ _ _) p lr = ff
no-parens {TYPE} {e} (ExTpAbs pi b pi' x Tk T) p lr = exprd-eq e TYPE && is-arrow p && not-left lr
no-parens {TYPE} {_} (ExTpIota pi pi' x oT T) p lr = ff
no-parens {TYPE} {_} (ExTpNoSpans T pi) p lr = tt
no-parens {TYPE} {_} (ExTpApp T T') p lr = is-arrow p -- || (is-type-level-app p && not-right lr)
no-parens {TYPE} {_} (ExTpAppt T t) p lr = is-arrow p -- || (is-type-level-app p && not-right lr)
no-parens {TYPE} {e} (ExTpArrow T a T') p lr = exprd-eq e TYPE && is-arrow p && not-left lr
no-parens {TYPE} {_} (ExTpEq _ t t' _) p lr = tt
no-parens {TYPE} {_} (ExTpHole pi) p lr = tt
no-parens {TYPE} {_} (ExTpLam pi pi' x Tk T) p lr = ff
no-parens {TYPE} {_} (ExTpParens pi T pi') p lr = tt
no-parens {TYPE} {_} (ExTpVar pi x) p lr = tt
no-parens {TYPE} {_} (ExTpLet _ _ _) _ _ = ff
no-parens {KIND} {_} (ExKdArrow k k') p lr = is-arrow p && not-left lr
no-parens {KIND} {_} (ExKdParens pi k pi') p lr = tt
no-parens {KIND} {_} (ExKdAbs pi pi' x Tk k) p lr = is-arrow p && not-left lr
no-parens {KIND} {_} (ExKdVar pi x as) p lr = tt
no-parens {KIND} {_} (ExKdStar pi) p lr = tt
no-parens {TPKD} _ _ _ = tt


decompose-apps' : ex-tm → ex-tm × ex-args
decompose-tpapps' : ex-tp → ex-tp × 𝕃 (ex-tm ⊎ ex-tp)
recompose-apps' : ex-args → ex-tm → ex-tm
recompose-tpapps' : 𝕃 (ex-tm ⊎ ex-tp) → ex-tp → ex-tp

decompose-apps' = h [] where
  h : ex-args → ex-tm → ex-tm × ex-args
  h acc (ExApp t me t') = h (ExTmArg me t' :: acc) t
  h acc (ExAppTp t T) = h (ExTpArg T :: acc) t
  h acc t = t , acc
decompose-tpapps' = h [] where
  h : 𝕃 (ex-tm ⊎ ex-tp) → ex-tp → ex-tp × 𝕃 (ex-tm ⊎ ex-tp)
  h acc (ExTpApp T T') = h (inj₂ T' :: acc) T
  h acc (ExTpAppt T t) = h (inj₁ t :: acc) T
  h acc T = T , acc
recompose-apps' = flip $ foldl λ {(ExTmArg me t') t → ExApp t me t'; (ExTpArg T) t → ExAppTp t T}
recompose-tpapps' = flip $ foldl λ {(inj₂ T') T → ExTpApp T T'; (inj₁ t) T → ExTpAppt T t}


pattern ced-ops-drop-spine = cedille-options.options.mk-options _ _ _ _ ff _ _ _ ff _
pattern ced-ops-conv-arr = cedille-options.options.mk-options _ _ _ _ _ _ _ _ ff _
pattern ced-ops-conv-abs = cedille-options.options.mk-options _ _ _ _ _ _ _ _ tt _

drop-spine : cedille-options.options → {ed : exprd} → ctxt → ⟦ ed ⟧' → ⟦ ed ⟧'
drop-spine ops @ ced-ops-drop-spine = h
  where
  drop-mod-args : ctxt → erased? → var × ex-args → var × ex-args
  drop-mod-args Γ me (v , as) =
    let qv = unqual-all (ctxt-get-qualif Γ) v in qv ,
    maybe-else' (maybe-if (~ v =string qv) ≫maybe ctxt-qualif-args-length Γ me qv)
      as (λ n → reverse (drop n (reverse as)))

  h : {ed : exprd} → ctxt → ⟦ ed ⟧' → ⟦ ed ⟧'
  h {TERM} Γ t with decompose-apps' t
  ...| ExVar _ x , as = uncurry (flip recompose-apps') $ map-fst (ExVar posinfo-gen) $ drop-mod-args Γ ff (x , as)
  ...| _ = t
  h {TYPE} Γ T with decompose-tpapps' T
  ...| ExTpVar _ x , as = uncurry (flip recompose-tpapps') $ map-fst (ExTpVar posinfo-gen) $ map-snd (map λ {(ExTmArg me t) → inj₁ t; (ExTpArg T) → inj₂ T}) $ drop-mod-args Γ ff (x , map (λ e → either-else' e (ExTmArg ff) ExTpArg) as)
  ...| _ = T
  h Γ x = x
drop-spine ops Γ x = x

to-string-rewrite : {ed : exprd} → ctxt → cedille-options.options → ⟦ ed ⟧' → Σi exprd ⟦_⟧'
to-string-rewrite{TERM} Γ ops (ExParens _ t _) = to-string-rewrite Γ ops t
to-string-rewrite{TYPE} Γ ops (ExTpParens _ T _) = to-string-rewrite Γ ops T
to-string-rewrite{KIND} Γ ops (ExKdParens _ k _) = to-string-rewrite Γ ops k
to-string-rewrite{TPKD} Γ ops (ExTkt T) = to-string-rewrite Γ ops T
to-string-rewrite{TPKD} Γ ops (ExTkk k) = to-string-rewrite Γ ops k
to-string-rewrite{TYPE} Γ ced-ops-conv-arr (ExTpAbs _ me _ ignored-var (ExTkt T) T') = , ExTpArrow T me T'
to-string-rewrite{KIND} Γ ced-ops-conv-arr (ExKdAbs _ _ ignored-var atk k) = , ExKdArrow atk k
to-string-rewrite{TYPE} Γ ced-ops-conv-abs (ExTpArrow T me T') = , ExTpAbs posinfo-gen me posinfo-gen ignored-var (ExTkt T) T'
to-string-rewrite{KIND} Γ ced-ops-conv-abs (ExKdArrow k k') = , ExKdAbs posinfo-gen posinfo-gen ignored-var k k'
--to-string-rewrite{LIFTINGTYPE} Γ ced-ops-conv-abs (LiftTpArrow T lT) = , LiftPi posinfo-gen ignored-var T lT
to-string-rewrite{TERM} Γ ops @ ced-ops-conv-abs (ExOpen _ _ _ _ t) = to-string-rewrite Γ ops t
to-string-rewrite{TERM} Γ ops (ExSigma pi t) with to-string-rewrite Γ ops t
...| ,_ {TERM} (ExSigma pi' t') = , t'
...| ,_ {TERM} t' = , ExSigma posinfo-gen t'
...| t? = , ExSigma posinfo-gen t
--to-string-rewrite{TERM} Γ ops (ExPhi pi eq t u pi') = , ExPhi pi eq t (erase u) pi'
--to-string-rewrite{TERM} Γ ops (ExRho pi op on eq og t) = , ExRho pi op on eq (flip maybe-map og λ _ → erase) t
--to-string-rewrite{TERM} Γ ops (ExBeta pi ot ot') = , ExBeta pi (maybe-map erase ot) (maybe-map erase ot')
to-string-rewrite{TERM} Γ ops (ExChi _ nothing t@(ExVar _ _)) = to-string-rewrite Γ ops t
--to-string-rewrite{TYPE} Γ ops (ExTpEq pi t₁ t₂ pi') = , ExTpEq pi (erase t₁) (erase t₂) pi'
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
strM = {ed : exprd} → DOC → ℕ → 𝕃 tag → ctxt → maybe ⟦ ed ⟧' → expr-side → DOC × ℕ × 𝕃 tag

strEmpty : strM
strEmpty s n ts Γ pe lr = s , n , ts

private to-stringh : {ed : exprd} → ⟦ ed ⟧' → strM

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


strFold' : (ℕ → ℕ) → {ed : exprd} → 𝕃 (ℕ × strM) → ℕ → 𝕃 tag → ctxt → maybe ⟦ ed ⟧' → expr-side → 𝕃 (ℕ × DOC) × ℕ × 𝕃 tag
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
term-to-stringh : ex-tm → strM
type-to-stringh : ex-tp → strM
kind-to-stringh : ex-kd → strM
--liftingType-to-stringh : liftingType → strM
tk-to-stringh : ex-tk → strM
ctr-to-string : ex-ctr → strM
--ctrs-to-string : ctrs → strM
case-to-string : ex-case → strM
cases-to-string : ex-cases → strM
caseArgs-to-string : 𝕃 ex-case-arg → strM → strM
let-to-string : erased? → def → strM → strM

params-to-string : ex-params → strM
params-to-string' : strM → ex-params → strM
params-to-string'' : ex-params → strM → strM
file-to-string : file → strM
cmds-to-string : cmds → strM → strM
cmd-to-string : cmd → strM → strM  
optTerm-to-string : maybe ex-tm → string → string → 𝕃 (ℕ × strM)
optClass-to-string : maybe ex-tk → strM
optGuide-to-string : maybe ex-guide → 𝕃 (ℕ × strM)
optNums-to-string : maybe (𝕃 num) → strM
optType-to-string : ℕ → maybe char → maybe ex-tp → 𝕃 (ℕ × strM)
lterms-to-string : 𝕃 lterm → strM
arg-to-string : ex-arg → strM
args-to-string : ex-args → strM
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

to-string-ed : {ed : exprd} → ⟦ ed ⟧' → strM
to-string-ed{TERM} = term-to-stringh
to-string-ed{TYPE} = type-to-stringh
to-string-ed{KIND} = kind-to-stringh
--to-string-ed{LIFTINGTYPE} = liftingType-to-stringh
to-string-ed{TPKD} = tk-to-stringh
--to-string-ed{ARG} = arg-to-string
--to-string-ed{QUALIF} q = strEmpty

to-stringh' : {ed : exprd} → expr-side → ⟦ ed ⟧' → strM
to-stringh' {ed} lr t {ed'} s n ts Γ mp lr' =
  elim-Σi (to-string-rewrite Γ options t) λ t' →
  parens-unless (~ isJust (mp ≫=maybe λ pe → maybe-if (~ no-parens t' pe lr)))
    (to-string-ed t') s n ts Γ (just t') lr
  where
  parens-unless : 𝔹 → strM → strM
  parens-unless p s = if p then s else (strAdd "(" ≫str strNest 1 s ≫str strAdd ")")

to-stringl : {ed : exprd} → ⟦ ed ⟧' → strM
to-stringr : {ed : exprd} → ⟦ ed ⟧' → strM
to-stringl = to-stringh' left
to-stringr = to-stringh' right
to-stringh = to-stringh' neither

set-parent : ∀ {ed} → ⟦ ed ⟧' → strM → strM
set-parent t m s n ts Γ _ lr = m s n ts Γ (just t) lr

apps-to-string : ∀ {ll : 𝔹} → (if ll then ex-tm else ex-tp) → strM
apps-to-string {tt} t with decompose-apps' t
...| tₕ , as = set-parent t $ strList 2 $ (to-stringl tₕ :: map arg-to-string as)
apps-to-string {ff} T with decompose-tpapps' T
...| Tₕ , as = set-parent T $ strList 2 $ (to-stringl Tₕ :: map (arg-to-string ∘ λ e → either-else' e (ExTmArg ff) ExTpArg) as)

lams-to-string : ex-tm → strM
lams-to-string t =
  elim-pair (decompose-lams-pretty t) λ xs b →
  set-parent t $ strBreak' $ foldr {B = 𝕃 (ℕ × strM)}
    (λ {(x , me , oc) r →
      (0 , strAdd (lam-to-string me) ≫str strAdd " " ≫str
        strBvar x (strNest 4 (optClass-to-string oc)) (strAdd " .")) ::
      map (map-snd $ strΓ' localScope x) r}) [ 2 , to-stringr b ] xs
  where
  decompose-lams-pretty : ex-tm → 𝕃 (var × erased? × maybe ex-tk) × ex-tm
  decompose-lams-pretty = h [] where
    h : 𝕃 (var × erased? × maybe ex-tk) → ex-tm → 𝕃 (var × erased? × maybe ex-tk) × ex-tm
    h acc (ExLam _ me _ x oc t) = h ((x , me , oc) :: acc) t
    h acc t = reverse acc , t

tk-to-stringh (ExTkt T) = to-stringh T
tk-to-stringh (ExTkk k) = to-stringh k

term-to-stringh (ExApp t me t') = apps-to-string (ExApp t me t')
term-to-stringh (ExAppTp t T) = apps-to-string (ExAppTp t T)
term-to-stringh (ExBeta pi ot ot') = strBreak' ((0 , strAdd "β") :: optTerm-to-string (maybe-map pos-tm-to-tm ot) "< " " >" ++ optTerm-to-string (maybe-map pos-tm-to-tm ot') "{ " " }") -- strBreak 3 0 (strAdd "β") 2 (optTerm-to-string ot "< " " >") 2 (optTerm-to-string ot' "{ " " }")}
term-to-stringh (ExChi pi mT t) = strBreak' ((0 , strAdd "χ") :: (optType-to-string 2 nothing mT) ++ (2 , strAdd "-") :: [ 2 , to-stringr t ])
term-to-stringh (ExDelta pi mT t) = strBreak' ((0 , strAdd "δ") :: (optType-to-string 2 nothing mT) ++ (2 , strAdd "-") :: [ 2 , to-stringr t ])
term-to-stringh (ExEpsilon pi lr m t) = strAdd "ε" ≫str strAdd (leftRight-to-string lr) ≫str strAdd (maybeMinus-to-string m) ≫str to-stringh t
term-to-stringh (ExHole pi) = strM-Γ λ Γ → strAddTags "●" (var-loc-tag Γ (split-var pi) "●")
term-to-stringh (ExIotaPair pi t t' og pi') = strBreak' ((1 , strAdd "[ " ≫str to-stringh t ≫str strAdd ",") :: (1 , to-stringh t')  :: optGuide-to-string og) ≫str strAdd " ]"
term-to-stringh (ExIotaProj t n pi) = to-stringh t ≫str strAdd ("." ^ n)
term-to-stringh (ExLam pi l pi' x oc t) = lams-to-string (ExLam pi l pi' x oc t)
term-to-stringh (ExLet pi fe dtT t) = let-to-string fe dtT (to-stringh t)
term-to-stringh (ExOpen pi o pi' x t) = strBreak 2 0 (strAdd (if o then "open " else "close ") ≫str strVar x ≫str strAdd " -") 2 (to-stringh t)
term-to-stringh (ExParens pi t pi') = to-stringh t
term-to-stringh (ExPhi pi eq t t' pi') = strBreak 3 0 (strAdd "φ " ≫str to-stringl eq ≫str strAdd " -") 2 (to-stringh t) 2 (strAdd "{ " ≫str to-stringr t' ≫str strAdd " }")
term-to-stringh (ExRho pi op on eq og t) = strBreak' ((0 , strAdd "ρ" ≫str strAdd (optPlus-to-string op) ≫str optNums-to-string on) :: (4 , to-stringl eq) :: (optGuide-to-string og) ++ [ 1 , strAdd "- " ≫str strNest 2 (to-stringr t) ])
term-to-stringh (ExSigma pi t) = strAdd "ς " ≫str to-stringh t
term-to-stringh (ExTheta pi theta t lts) = theta-to-string theta ≫str to-stringh t ≫str lterms-to-string lts
term-to-stringh (ExVar pi x) = strVar x
term-to-stringh (ExMu pi (ExIsMu pi' x) t ot pi'' cs pi''') = strAdd "μ " ≫str strBvar x (strAdd " . " ≫str strBreak' ((2 , to-stringl t) :: (optType-to-string 3 (just '@') ot))) (strAdd " " ≫str strBracket '{' '}' (cases-to-string cs))
term-to-stringh (ExMu pi (ExIsMu' ot) t oT pi' cs pi'') = strAdd "μ' " ≫str strBreak' ((optTerm-to-string ot " < " " > ") ++ (2 , to-stringl t) :: (optType-to-string 3 (just '@') oT)) ≫str strAdd " " ≫str strBracket '{' '}' (cases-to-string cs)

type-to-stringh (ExTpAbs pi b pi' x Tk T) = strBreak 2 3 (strAdd (binder-to-string b ^ " ") ≫str strBvar x (strAdd " : " ≫str to-stringl Tk ≫str strAdd " .") strEmpty) 1 (strΓ' localScope x (to-stringh T))
type-to-stringh (ExTpIota pi pi' x T T') = strBreak 2 2 (strAdd "ι " ≫str strBvar x (strAdd " : " ≫str to-stringh T ≫str strAdd " .") strEmpty) 2 (strΓ' localScope x (to-stringh T'))
--type-to-stringh (Lft pi pi' x t lT) = strAdd "↑ " ≫str strBvar x (strAdd " . ") (to-stringh t) ≫str strAdd " : " ≫str to-stringh lT
type-to-stringh (ExTpNoSpans T pi) = to-string-ed T
type-to-stringh (ExTpApp T T') = apps-to-string (ExTpApp T T')
type-to-stringh (ExTpAppt T t) = apps-to-string (ExTpAppt T t)
type-to-stringh (ExTpArrow T a T') = strBreak 2 2 (to-stringl T ≫str strAdd (arrowtype-to-string a)) 2 (to-stringr T')
type-to-stringh (ExTpEq _ t t' _) = strAdd "{ " ≫str to-stringh t ≫str strAdd " ≃ " ≫str to-stringh t' ≫str strAdd " }"
type-to-stringh (ExTpHole pi) = strM-Γ λ Γ → strAddTags "●" (var-loc-tag Γ (split-var pi) "●")
type-to-stringh (ExTpLam pi pi' x Tk T) = strBreak 2 3 (strAdd "λ " ≫str strBvar x (strAdd " : " ≫str tk-to-stringh Tk ≫str strAdd " .") strEmpty) 1 (strΓ' localScope x (to-stringr T))
type-to-stringh (ExTpParens pi T pi') = to-stringh T
type-to-stringh (ExTpVar pi x) = strVar x
type-to-stringh (ExTpLet pi dtT T) = let-to-string NotErased dtT (to-stringh T)

kind-to-stringh (ExKdArrow k k') = strBreak 2 2 (to-stringl k ≫str strAdd " ➔") 2 (to-stringr k')
kind-to-stringh (ExKdParens pi k pi') = to-stringh k
kind-to-stringh (ExKdAbs pi pi' x Tk k) = strBreak 2 4 (strAdd "Π " ≫str strBvar x (strAdd " : " ≫str to-stringl Tk ≫str strAdd " .") strEmpty) 1 (strΓ' localScope x (to-stringh k))
--kind-to-stringh (KndTpArrow T k) = strBreak 2 2 (to-stringl T ≫str strAdd " ➔") 2 (to-stringr k)
kind-to-stringh (ExKdVar pi x as) = strList 2 (strKvar x :: map arg-to-string as)
kind-to-stringh (ExKdStar pi) = strAdd "★"

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
optGuide-to-string nothing = []
optGuide-to-string (just (ExGuide pi v T)) = [ 2 , strAdd "@ " ≫str strBvar v (strAdd " . ") (to-stringh T) ]
optType-to-string i pfx nothing = []
optType-to-string i pfx (just T) = [ i , maybe-else strEmpty (λ pfx → strAdd (𝕃char-to-string (pfx :: [ ' ' ]))) pfx ≫str to-stringh T ]
lterms-to-string (Lterm m t :: ts) = strAdd (" " ^ maybeErased-to-string m) ≫str to-stringh t ≫str lterms-to-string ts
lterms-to-string [] = strEmpty
arg-to-string (ExTmArg tt t) = strAdd "-" ≫str strNest 1 (to-stringh t)
arg-to-string (ExTmArg ff t) = to-stringh t
arg-to-string (ExTpArg T) = strAdd "·" ≫str strNest 2 (to-stringh T)
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
optNums-to-string nothing = strEmpty
optNums-to-string (just ns) = strAdd "<" ≫str nums-to-string ns ≫str strAdd ">"
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
ctr-to-string (ExCtr _ x T) = strAdd x ≫str strAdd " : " ≫str to-stringh T
case-to-string (ExCase _ x as t) =
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
caseArgs-to-string (ExCaseArg CaseArgTm pi x :: as) m = strAdd " " ≫str strBvar x strEmpty (caseArgs-to-string as m)
caseArgs-to-string (ExCaseArg CaseArgEr pi x :: as) m = strAdd " -" ≫str strBvar x strEmpty (caseArgs-to-string as m)
caseArgs-to-string (ExCaseArg CaseArgTp pi x :: as) m = strAdd " ·" ≫str strBvar x strEmpty (caseArgs-to-string as m)

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
param-to-string (ExParam pi me pi' v atk _) =
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

resugar : ∀ {ed} → (erase : 𝔹) → ⟦ ed ⟧ → ⟦ ed ⟧'
resugar b t = {!!}

to-stringe : {ed : exprd} → ⟦ ed ⟧ → strM
to-stringe = to-stringh ∘ resugar (cedille-options.options.erase-types options)

tpkd-to-stringe = to-stringe {TPKD}

to-string-tag : {ed : exprd} → string → ctxt → ⟦ ed ⟧ → tagged-val
to-string-tag name Γ t = strRunTag name Γ (to-stringe t)

to-string : {ed : exprd} → ctxt → ⟦ ed ⟧' → rope
to-string Γ t = strRun Γ (to-stringh t)


tpkd-to-string : ctxt → tpkd → rope
tpkd-to-string Γ atk = strRun Γ (tpkd-to-stringe atk)

params-to-string-tag : string → ctxt → ex-params → tagged-val
params-to-string-tag name Γ ps = strRunTag name Γ (params-to-string ps)

