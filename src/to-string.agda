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
open import erase

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
exprd-eq TK TK = tt
exprd-eq LIFTINGTYPE LIFTINGTYPE = tt
exprd-eq QUALIF QUALIF = tt
exprd-eq ARG ARG = tt
exprd-eq _ _ = ff

no-parens : {ed : exprd} → {ed' : exprd} → ⟦ ed ⟧ → ⟦ ed' ⟧ → expr-side → 𝔹
no-parens {_} {TERM} _ (IotaPair pi t t' og pi') lr = tt
no-parens {_} {TYPE} _ (TpEq _ t t' _) lr = tt
no-parens {_} {TERM} _ (Beta pi ot ot') lr = tt
no-parens {_} {TERM} _ (Phi pi eq t t' pi') right = tt
no-parens {_} {TERM} _ (Phi pi eq t t' pi') neither = tt
no-parens {_} {TERM} _ (Rho _ _ _ _ _ _) right = tt
no-parens {_} {TERM} _ (Chi _ _ _) right = tt
no-parens {_} {TERM} _ (Delta _ _ _) right = tt
no-parens {_} {TERM} _ (Let _ _ _ _) lr = tt
no-parens {_} {TERM} _ (Lam _ _ _ _ _ _) lr = tt
no-parens {_} {TERM} _ (Mu _ _ _ _ _ _ _ _) right = tt
no-parens {_} {TERM} _ (Mu' _ _ _ _ _ _ _) right = tt
no-parens {_} {TYPE} _ (TpLambda _ _ _ _ _) lr = tt
no-parens {_} {TYPE} _ (Abs _ _ _ _ _ _) lr = tt
no-parens {_} {KIND} _ (KndPi _ _ _ _ _) neither = tt
no-parens {_} {TYPE} _ (Iota _ _ _ _ _) lr = tt
no-parens {_} {LIFTINGTYPE} _ (LiftPi _ _ _ _) lr = tt
no-parens {TERM} {_} (App t me t') p lr = ff --is-term-level-app p && not-right lr
no-parens {TERM} {_} (AppTp t T) p lr = ff --is-term-level-app p && not-right lr
no-parens {TERM} {_} (Beta pi ot ot') p lr = tt
no-parens {TERM} {_} (Chi pi mT t) p lr = ff
no-parens {TERM} {_} (Delta pi mT t) p lr = ff
no-parens {TERM} {_} (Epsilon pi lr' m t) p lr = is-eq-op p
no-parens {TERM} {_} (Hole pi) p lr = tt
no-parens {TERM} {_} (IotaPair pi t t' og pi') p lr = tt
no-parens {TERM} {_} (IotaProj t n pi) p lr = tt
no-parens {TERM} {_} (Lam pi l' pi' x oc t) p lr = ff
no-parens {TERM} {_} (Let pi _ dtT t) p lr = ff
no-parens {TERM} {_} (Open _ _ _ _ _) p lr = ff
no-parens {TERM} {_} (Parens pi t pi') p lr = tt
no-parens {TERM} {_} (Phi pi eq t t' pi') p lr = ff
no-parens {TERM} {_} (Rho pi op on eq og t) p lr = ff
no-parens {TERM} {_} (Sigma pi t) p lr = is-eq-op p
no-parens {TERM} {_} (Theta pi theta t lts) p lr = ff
no-parens {TERM} {_} (Var pi x) p lr = tt
no-parens {TERM} {_} (Mu _ _ _ _ _ _ _ _) p lr = ff
no-parens {TERM} {_} (Mu' _ _ _ _ _ _ _)  p lr = ff
no-parens {TYPE} {e} (Abs pi b pi' x Tk T) p lr = exprd-eq e TYPE && is-arrow p && not-left lr
no-parens {TYPE} {_} (Iota pi pi' x oT T) p lr = ff
no-parens {TYPE} {_} (Lft pi pi' x t lT) p lr = ff
no-parens {TYPE} {_} (NoSpans T pi) p lr = tt
no-parens {TYPE} {_} (TpApp T T') p lr = is-arrow p -- || (is-type-level-app p && not-right lr)
no-parens {TYPE} {_} (TpAppt T t) p lr = is-arrow p -- || (is-type-level-app p && not-right lr)
no-parens {TYPE} {e} (TpArrow T a T') p lr = exprd-eq e TYPE && is-arrow p && not-left lr
no-parens {TYPE} {_} (TpEq _ t t' _) p lr = tt
no-parens {TYPE} {_} (TpHole pi) p lr = tt
no-parens {TYPE} {_} (TpLambda pi pi' x Tk T) p lr = ff
no-parens {TYPE} {_} (TpParens pi T pi') p lr = tt
no-parens {TYPE} {_} (TpVar pi x) p lr = tt
no-parens {TYPE} {_} (TpLet _ _ _) _ _ = ff
no-parens {KIND} {_} (KndArrow k k') p lr = is-arrow p && not-left lr
no-parens {KIND} {_} (KndParens pi k pi') p lr = tt
no-parens {KIND} {_} (KndPi pi pi' x Tk k) p lr = is-arrow p && not-left lr
no-parens {KIND} {_} (KndTpArrow T k) p lr = is-arrow p && not-left lr
no-parens {KIND} {_} (KndVar pi x as) p lr = tt
no-parens {KIND} {_} (Star pi) p lr = tt
no-parens {LIFTINGTYPE} (LiftArrow lT lT') p lr = is-arrow p && not-left lr
no-parens {LIFTINGTYPE} (LiftParens pi lT pi') p lr = tt
no-parens {LIFTINGTYPE} (LiftPi pi x T lT) p lr = is-arrow p && not-left lr
no-parens {LIFTINGTYPE} (LiftStar pi) p lr = tt
no-parens {LIFTINGTYPE} (LiftTpArrow T lT) p lr = is-arrow p && not-left lr
no-parens {TK} _ _ _ = tt
no-parens {QUALIF} _ _ _ = tt
no-parens {ARG} _ _ _ = tt

pattern ced-ops-drop-spine = cedille-options.options.mk-options _ _ _ _ ff _ _ _ ff _
pattern ced-ops-conv-arr = cedille-options.options.mk-options _ _ _ _ _ _ _ _ ff _
pattern ced-ops-conv-abs = cedille-options.options.mk-options _ _ _ _ _ _ _ _ tt _

drop-spine : cedille-options.options → {ed : exprd} → ctxt → ⟦ ed ⟧ → ⟦ ed ⟧
drop-spine ops @ ced-ops-drop-spine = h
  where
  drop-mod-args : ctxt → maybeErased → spineApp → spineApp
  drop-mod-args Γ me (v , as) =
    let qv = unqual-all (ctxt-get-qualif Γ) v in qv ,
    maybe-else' (maybe-if (~ v =string qv) ≫maybe ctxt-qualif-args-length Γ me qv)
      as (λ n → reverse (drop n (reverse as)))

  h : {ed : exprd} → ctxt → ⟦ ed ⟧ → ⟦ ed ⟧
  h {TERM} Γ t = maybe-else' (term-to-spapp t) t (spapp-term ∘ drop-mod-args Γ (cedille-options.options.erase-types ops))
  h {TYPE} Γ T = maybe-else' (type-to-spapp T) T (spapp-type ∘ drop-mod-args Γ NotErased)
  h Γ x = x
drop-spine ops Γ x = x

to-string-rewrite : {ed : exprd} → ctxt → cedille-options.options → ⟦ ed ⟧ → Σi exprd ⟦_⟧
to-string-rewrite{TERM} Γ ops (Parens _ t _) = to-string-rewrite Γ ops t
to-string-rewrite{TYPE} Γ ops (TpParens _ T _) = to-string-rewrite Γ ops T
to-string-rewrite{KIND} Γ ops (KndParens _ k _) = to-string-rewrite Γ ops k
to-string-rewrite{LIFTINGTYPE} Γ ops (LiftParens _ lT _) = to-string-rewrite Γ ops lT
to-string-rewrite{TK} Γ ops (Tkt T) = to-string-rewrite Γ ops T
to-string-rewrite{TK} Γ ops (Tkk k) = to-string-rewrite Γ ops k
to-string-rewrite{TYPE} Γ ced-ops-conv-arr (Abs _ me _ ignored-var (Tkt T) T') = , TpArrow T me T'
to-string-rewrite{KIND} Γ ced-ops-conv-arr (KndPi _ _ ignored-var (Tkt T) k) = , KndTpArrow T k
to-string-rewrite{KIND} Γ ced-ops-conv-arr (KndPi _ _ ignored-var (Tkk k) k') = , KndArrow k k'
to-string-rewrite{LIFTINGTYPE} Γ ced-ops-conv-arr (LiftPi _ ignored-var T lT) = , LiftTpArrow T lT
to-string-rewrite{TYPE} Γ ced-ops-conv-abs (TpArrow T me T') = , Abs posinfo-gen me posinfo-gen ignored-var (Tkt T) T'
to-string-rewrite{KIND} Γ ced-ops-conv-abs (KndTpArrow T k) = , KndPi posinfo-gen posinfo-gen ignored-var (Tkt T) k
to-string-rewrite{KIND} Γ ced-ops-conv-abs (KndArrow k k') = , KndPi posinfo-gen posinfo-gen ignored-var (Tkk k) k'
to-string-rewrite{LIFTINGTYPE} Γ ced-ops-conv-abs (LiftTpArrow T lT) = , LiftPi posinfo-gen ignored-var T lT
to-string-rewrite{TERM} Γ ops @ ced-ops-conv-abs (Open _ _ _ _ t) = to-string-rewrite Γ ops t
to-string-rewrite{TERM} Γ ops (Sigma pi t) with to-string-rewrite Γ ops t
...| ,_ {TERM} (Sigma pi' t') = , t'
...| ,_ {TERM} t' = , Sigma posinfo-gen t'
...| t? = , Sigma posinfo-gen t
to-string-rewrite{TERM} Γ ops (Phi pi eq t u pi') = , Phi pi eq t (erase u) pi'
to-string-rewrite{TERM} Γ ops (Rho pi op on eq og t) = , Rho pi op on eq (optGuide-map og λ _ → erase) t
to-string-rewrite{TERM} Γ ops (Beta pi ot ot') = , Beta pi (optTerm-map ot erase) (optTerm-map ot' erase)
to-string-rewrite{TERM} Γ ops (Chi _ NoType t @ (Var _ _)) = to-string-rewrite Γ ops t
to-string-rewrite{TYPE} Γ ops (TpEq pi t₁ t₂ pi') = , TpEq pi (erase t₁) (erase t₂) pi'
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

var-tags : ctxt → qvar → var → 𝕃 (string × 𝕃 tag)
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
liftingType-to-stringh : liftingType → strM
tk-to-stringh : tk → strM
ctr-to-string : ctr → strM
--ctrs-to-string : ctrs → strM
case-to-string : case → strM
cases-to-string : cases → strM
caseArgs-to-string : caseArgs → strM → strM
let-to-string : maybeErased → defTermOrType → strM → strM

params-to-string : params → strM
params-to-string' : strM → params → strM
params-to-string'' : params → strM → strM
file-to-string : start → strM
cmds-to-string : cmds → strM → strM
cmd-to-string : cmd → strM → strM  
optTerm-to-string : optTerm → string → string → 𝕃 (ℕ × strM)
optClass-to-string : optClass → strM
optGuide-to-string : optGuide → 𝕃 (ℕ × strM)
optNums-to-string : optNums → strM
optType-to-string : ℕ → maybe char → optType → 𝕃 (ℕ × strM)
lterms-to-string : lterms → strM
arg-to-string : arg → strM
args-to-string : args → strM
binder-to-string : maybeErased → string
opacity-to-string : opacity → string
maybeErased-to-string : maybeErased → string
lam-to-string : maybeErased → string
leftRight-to-string : leftRight → string
vars-to-string : vars → strM
nums-to-string : nums → strM
theta-to-string : theta → strM
arrowtype-to-string : maybeErased → string
maybeMinus-to-string : maybeMinus → string
optPlus-to-string : rhoHnf → string
optPublic-to-string : optPublic → string
optAs-to-string : optAs → strM
bracketL : maybeErased → string
bracketR : maybeErased → string
braceL : maybeErased → string
braceR : maybeErased → string

to-string-ed : {ed : exprd} → ⟦ ed ⟧ → strM
to-string-ed{TERM} = term-to-stringh
to-string-ed{TYPE} = type-to-stringh
to-string-ed{KIND} = kind-to-stringh
to-string-ed{LIFTINGTYPE} = liftingType-to-stringh
to-string-ed{TK} = tk-to-stringh
to-string-ed{ARG} = arg-to-string
to-string-ed{QUALIF} q = strEmpty

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


set-parent : ∀ {ed} → ⟦ ed ⟧ → strM → strM
set-parent t m s n ts Γ _ lr = m s n ts Γ (just t) lr

apps-to-string : ∀ {ll : 𝔹} → (if ll then term else type) → strM
apps-to-string {tt} t with decompose-apps t
...| tₕ , as = set-parent t $ strList 2 $ (to-stringl tₕ :: map arg-to-string as)
apps-to-string {ff} T with decompose-tpapps T
...| Tₕ , as = set-parent T $ strList 2 $ (to-stringl Tₕ :: map (arg-to-string ∘ tty-to-arg NotErased) as)

lams-to-string : term → strM
lams-to-string t =
  elim-pair (decompose-lams-pretty t) λ xs b →
  set-parent t $ strBreak' $ foldr {B = 𝕃 (ℕ × strM)}
    (λ {(x , me , oc) r →
      (0 , strAdd (lam-to-string me) ≫str strAdd " " ≫str
        strBvar x (strNest 4 (optClass-to-string oc)) (strAdd " .")) ::
      map (map-snd $ strΓ' localScope x) r}) [ 2 , to-stringr b ] xs
  where
  decompose-lams-pretty : term → 𝕃 (var × maybeErased × optClass) × term
  decompose-lams-pretty = h [] where
    h : 𝕃 (var × maybeErased × optClass) → term → 𝕃 (var × maybeErased × optClass) × term
    h acc (Lam _ me _ x oc t) = h ((x , me , oc) :: acc) t
    h acc t = reverse acc , t

tk-to-stringh (Tkt T) = to-stringh T
tk-to-stringh (Tkk k) = to-stringh k

term-to-stringh (App t me t') = apps-to-string (App t me t')
term-to-stringh (AppTp t T) = apps-to-string (AppTp t T)
term-to-stringh (Beta pi ot ot') = strBreak' ((0 , strAdd "β") :: optTerm-to-string ot "< " " >" ++ optTerm-to-string ot' "{ " " }") -- strBreak 3 0 (strAdd "β") 2 (optTerm-to-string ot "< " " >") 2 (optTerm-to-string ot' "{ " " }")}
term-to-stringh (Chi pi mT t) = strBreak' ((0 , strAdd "χ") :: (optType-to-string 2 nothing mT) ++ (2 , strAdd "-") :: [ 2 , to-stringr t ])
term-to-stringh (Delta pi mT t) = strBreak' ((0 , strAdd "δ") :: (optType-to-string 2 nothing mT) ++ (2 , strAdd "-") :: [ 2 , to-stringr t ])
term-to-stringh (Epsilon pi lr m t) = strAdd "ε" ≫str strAdd (leftRight-to-string lr) ≫str strAdd (maybeMinus-to-string m) ≫str to-stringh t
term-to-stringh (Hole pi) = strM-Γ λ Γ → strAddTags "●" (var-loc-tag Γ (split-var pi) "●")
term-to-stringh (IotaPair pi t t' og pi') = strBreak' ((1 , strAdd "[ " ≫str to-stringh t ≫str strAdd ",") :: (1 , to-stringh t')  :: optGuide-to-string og) ≫str strAdd " ]"
term-to-stringh (IotaProj t n pi) = to-stringh t ≫str strAdd ("." ^ n)
term-to-stringh (Lam pi l pi' x oc t) = lams-to-string (Lam pi l pi' x oc t)
term-to-stringh (Let pi fe dtT t) = let-to-string fe dtT (to-stringh t)
term-to-stringh (Open pi o pi' x t) = strBreak 2 0 (strAdd (if o iff OpacTrans then "open " else "close ") ≫str strVar x ≫str strAdd " -") 2 (to-stringh t)
term-to-stringh (Parens pi t pi') = to-stringh t
term-to-stringh (Phi pi eq t t' pi') = strBreak 3 0 (strAdd "φ " ≫str to-stringl eq ≫str strAdd " -") 2 (to-stringh t) 2 (strAdd "{ " ≫str to-stringr t' ≫str strAdd " }")
term-to-stringh (Rho pi op on eq og t) = strBreak' ((0 , strAdd "ρ" ≫str strAdd (optPlus-to-string op) ≫str optNums-to-string on) :: (4 , to-stringl eq) :: (optGuide-to-string og) ++ [ 1 , strAdd "- " ≫str to-stringr t ])
term-to-stringh (Sigma pi t) = strAdd "ς " ≫str to-stringh t
term-to-stringh (Theta pi theta t lts) = theta-to-string theta ≫str to-stringh t ≫str lterms-to-string lts
term-to-stringh (Var pi x) = strVar x
term-to-stringh (Mu pi pi' x t ot pi'' cs pi''') = strAdd "μ " ≫str strBvar x (strAdd " . " ≫str strBreak' ((2 , to-stringl t) :: (optType-to-string 3 (just '@') ot))) (strAdd " " ≫str strBracket '{' '}' (cases-to-string cs))
term-to-stringh (Mu' pi ot t oT pi' cs pi'') = strAdd "μ' " ≫str strBreak' ((optTerm-to-string ot " < " " > ") ++ (2 , to-stringl t) :: (optType-to-string 3 (just '@') oT)) ≫str strAdd " " ≫str strBracket '{' '}' (cases-to-string cs)

type-to-stringh (Abs pi b pi' x Tk T) = strBreak 2 3 (strAdd (binder-to-string b ^ " ") ≫str strBvar x (strAdd " : " ≫str to-stringl Tk ≫str strAdd " .") strEmpty) 1 (strΓ' localScope x (to-stringh T))
type-to-stringh (Iota pi pi' x T T') = strBreak 2 2 (strAdd "ι " ≫str strBvar x (strAdd " : " ≫str to-stringh T ≫str strAdd " .") strEmpty) 2 (strΓ' localScope x (to-stringh T'))
type-to-stringh (Lft pi pi' x t lT) = strAdd "↑ " ≫str strBvar x (strAdd " . ") (to-stringh t) ≫str strAdd " : " ≫str to-stringh lT
type-to-stringh (NoSpans T pi) = to-string-ed T
type-to-stringh (TpApp T T') = apps-to-string (TpApp T T')
type-to-stringh (TpAppt T t) = apps-to-string (TpAppt T t)
type-to-stringh (TpArrow T a T') = strBreak 2 2 (to-stringl T ≫str strAdd (arrowtype-to-string a)) 2 (to-stringr T')
type-to-stringh (TpEq _ t t' _) = strAdd "{ " ≫str to-stringh (erase-term t) ≫str strAdd " ≃ " ≫str to-stringh (erase-term t') ≫str strAdd " }"
type-to-stringh (TpHole pi) = strM-Γ λ Γ → strAddTags "●" (var-loc-tag Γ (split-var pi) "●")
type-to-stringh (TpLambda pi pi' x Tk T) = strBreak 2 3 (strAdd "λ " ≫str strBvar x (strAdd " : " ≫str tk-to-stringh Tk ≫str strAdd " .") strEmpty) 1 (strΓ' localScope x (to-stringr T))
type-to-stringh (TpParens pi T pi') = to-stringh T
type-to-stringh (TpVar pi x) = strVar x
type-to-stringh (TpLet pi dtT T) = let-to-string NotErased dtT (to-stringh T)

kind-to-stringh (KndArrow k k') = strBreak 2 2 (to-stringl k ≫str strAdd " ➔") 2 (to-stringr k')
kind-to-stringh (KndParens pi k pi') = to-stringh k
kind-to-stringh (KndPi pi pi' x Tk k) = strBreak 2 4 (strAdd "Π " ≫str strBvar x (strAdd " : " ≫str to-stringl Tk ≫str strAdd " .") strEmpty) 1 (strΓ' localScope x (to-stringh k))
kind-to-stringh (KndTpArrow T k) = strBreak 2 2 (to-stringl T ≫str strAdd " ➔") 2 (to-stringr k)
kind-to-stringh (KndVar pi x as) = strList 2 (strKvar x :: map arg-to-string as)
kind-to-stringh (Star pi) = strAdd "★"

liftingType-to-stringh (LiftArrow lT lT') = to-stringl lT ≫str strAdd " ➔↑ " ≫str to-stringr lT'
liftingType-to-stringh (LiftParens pi lT pi') = strAdd "(" ≫str to-string-ed lT ≫str strAdd ")"
liftingType-to-stringh (LiftPi pi x T lT) = strAdd "Π↑ " ≫str strBvar x (strAdd " : " ≫str to-stringh T ≫str strAdd " . ") (to-stringh lT)
liftingType-to-stringh (LiftStar pi) = strAdd "☆"
liftingType-to-stringh (LiftTpArrow T lT) = to-stringl T ≫str strAdd " ➔↑ " ≫str to-stringr lT
optTerm-to-string NoTerm c1 c2 = []
optTerm-to-string (SomeTerm t _) c1 c2 = [ string-length c1 , strAdd c1 ≫str to-stringh t  ≫str strAdd c2 ]
optClass-to-string NoClass = strEmpty
optClass-to-string (SomeClass Tk) = strAdd " : " ≫str tk-to-stringh Tk
optGuide-to-string NoGuide = []
optGuide-to-string (Guide pi v T) = [ 2 , strAdd "@ " ≫str strBvar v (strAdd " . ") (to-stringh T) ]
optType-to-string i pfx NoType = []
optType-to-string i pfx (SomeType T) = [ i , maybe-else strEmpty (λ pfx → strAdd (𝕃char-to-string (pfx :: [ ' ' ]))) pfx ≫str to-stringh T ]
lterms-to-string (Lterm m t :: ts) = strAdd (" " ^ maybeErased-to-string m) ≫str to-stringh t ≫str lterms-to-string ts
lterms-to-string [] = strEmpty
arg-to-string (TermArg Erased t) = strAdd "-" ≫str strNest 1 (to-stringh t)
arg-to-string (TermArg NotErased t) = to-stringh t
arg-to-string (TypeArg T) = strAdd "· " ≫str strNest 2 (to-stringh T)
args-to-string = foldr' strEmpty λ t x → strAdd " " ≫str arg-to-string t ≫str x
binder-to-string All = "∀"
binder-to-string Pi = "Π"
opacity-to-string OpacOpaque = "opaque "
opacity-to-string OpacTrans = ""
maybeErased-to-string Erased = "-"
maybeErased-to-string NotErased = ""
lam-to-string Erased = "Λ"
lam-to-string NotErased = "λ"
leftRight-to-string Left = "l"
leftRight-to-string Right = "r"
leftRight-to-string Both = ""
vars-to-string (VarsStart v) = strVar v
vars-to-string (VarsNext v vs) = strVar v ≫str strAdd " " ≫str vars-to-string vs
theta-to-string Abstract = strAdd "θ "
theta-to-string AbstractEq = strAdd "θ+ "
theta-to-string (AbstractVars vs) = strAdd "θ<" ≫str vars-to-string vs ≫str strAdd "> "
nums-to-string (NumsStart n) = strAdd n
nums-to-string (NumsNext n ns) = strAdd n ≫str strAdd " " ≫str nums-to-string ns
optNums-to-string NoNums = strEmpty
optNums-to-string (SomeNums ns) = strAdd "<" ≫str nums-to-string ns ≫str strAdd ">"
arrowtype-to-string NotErased = " ➔"
arrowtype-to-string Erased = " ➾"
maybeMinus-to-string EpsHnf = ""
maybeMinus-to-string EpsHanf = "-"
optPlus-to-string RhoPlain = ""
optPlus-to-string RhoPlus = "+"
optPublic-to-string NotPublic = ""
optPublic-to-string IsPublic = "public "
optAs-to-string NoOptAs = strEmpty
optAs-to-string (SomeOptAs _ x) = strAdd " as " ≫str strAdd x
ctr-to-string (Ctr _ x T) = strAdd x ≫str strAdd " : " ≫str to-stringh T
case-to-string (Case _ x as t) =
  strM-Γ λ Γ →
  let as-f = λ x as → strVar x ≫str caseArgs-to-string as (strAdd " ➔ " ≫str to-stringr t) in
  case (env-lookup Γ x , options) of uncurry λ where
    (just (ctr-def mps T _ _ _ , _ , _)) ced-ops-drop-spine →
          as-f (unqual-all (ctxt-get-qualif Γ) x) as
    _ _ → as-f x as

cases-to-string = h use-newlines where
  h : 𝔹 → cases → strM
  h _ [] = strEmpty
  h tt (m :: []) = strAdd "| " ≫str case-to-string m
  h tt (m :: ms) = strAdd "| " ≫str case-to-string m ≫str strLine ≫str h tt ms
  h ff (m :: []) = case-to-string m
  h ff (m :: ms) = case-to-string m ≫str strAdd " | " ≫str h ff ms

caseArgs-to-string [] m = m
caseArgs-to-string (CaseTermArg pi me x :: as) m = strAdd (" " ^ maybeErased-to-string me) ≫str strBvar x strEmpty (caseArgs-to-string as m)
caseArgs-to-string (CaseTypeArg pi x :: as) m = strAdd " · " ≫str strBvar x strEmpty (caseArgs-to-string as m)

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

param-to-string : decl → (strM → strM) × strM
param-to-string (Decl _ pi me v atk _) =
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

file-to-string (File is _ _ mn ps cs _) =
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
  
cmd-to-string (DefTermOrType op (DefTerm pi x mcT t) _) f =
  strM-Γ λ Γ →
  let ps = ctxt-get-current-params Γ
      ps' = if pi =string elab-hide-key then params-set-erased Erased ps else ps in
  strBreak'
    ((2 , strAdd (opacity-to-string op) ≫str strAdd x) ::
     optType-to-string 4 (just ':') (optType-map mcT $ abs-expand-type ps') ++
     [ 2 , strAdd "= " ≫str to-stringh (lam-expand-term ps' t) ≫str strAdd " ." ]) ≫str
  strΓ' globalScope x f
cmd-to-string (DefTermOrType op (DefType pi x k T) _) f =
  strM-Γ λ Γ →
  let ps = ctxt-get-current-params Γ
      ps' = if pi =string elab-hide-key then params-set-erased Erased ps else ps in
  strBreak'
    ((2 , strAdd (opacity-to-string op) ≫str strAdd x) ::
     (4 , strAdd ": " ≫str to-stringh (abs-expand-kind ps' k)) ::
     [ 2 , strAdd "= " ≫str to-stringh (lam-expand-type ps' T) ≫str strAdd " ." ]) ≫str
  strΓ' globalScope x f
cmd-to-string (DefKind pi x ps k _) f =
  strM-Γ λ Γ →
  let ps' = ctxt-get-current-params Γ in
  strAdd x ≫str
  params-to-string'' (ps' ++ ps)
  (strAdd " = " ≫str
   to-stringh k ≫str
   strAdd " .") ≫str
  strΓ' globalScope x f
cmd-to-string (ImportCmd (Import _ op _ fn oa as _)) f =
  strAdd "import " ≫str
  strAdd (optPublic-to-string op) ≫str
  strAdd fn ≫str
  optAs-to-string oa ≫str
  strList 2 (strEmpty :: map arg-to-string as) ≫str
  strAdd " ." ≫str
  f
cmd-to-string (DefDatatype (Datatype pi pi' x ps k cs ) pi'') f =
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

to-stringe : {ed : exprd} → ⟦ ed ⟧ → strM
to-stringe with cedille-options.options.erase-types options
...| tt = to-stringh ∘ erase
...| ff = to-stringh

tk-to-stringe = to-stringe {TK}

to-string-tag : {ed : exprd} → string → ctxt → ⟦ ed ⟧ → tagged-val
to-string-tag name Γ t = strRunTag name Γ
  (to-stringh
    (if cedille-options.options.erase-types options
       then erase t
       else t))

to-string : {ed : exprd} → ctxt → ⟦ ed ⟧ → rope
to-string Γ t = strRun Γ (to-stringh t)


tk-to-string : ctxt → tk → rope
tk-to-string Γ atk = strRun Γ (tk-to-stringe atk)

params-to-string-tag : string → ctxt → params → tagged-val
params-to-string-tag name Γ ps = strRunTag name Γ (params-to-string ps)

