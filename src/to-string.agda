import cedille-options

module to-string (options : cedille-options.options) where

open import lib
open import cedille-types
open import constants
open import syntax-util
open import ctxt
open import rename
open import general-util

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
no-parens {_} {KIND} _ (KndPi _ _ _ _ _) lr = tt
no-parens {_} {TYPE} _ (Iota _ _ _ _ _) lr = tt
no-parens {_} {LIFTINGTYPE} _ (LiftPi _ _ _ _) lr = tt
no-parens{TERM} (App t me t') p lr = is-term-level-app p && not-right lr
no-parens{TERM} (AppTp t T) p lr = is-term-level-app p && not-right lr
no-parens{TERM} (Beta pi ot ot') p lr = tt
no-parens{TERM} (Chi pi mT t) p lr = ff
no-parens{TERM} (Delta pi mT t) p lr = ff
no-parens{TERM} (Epsilon pi lr' m t) p lr = is-eq-op p
no-parens{TERM} (Hole pi) p lr = tt
no-parens{TERM} (IotaPair pi t t' og pi') p lr = tt
no-parens{TERM} (IotaProj t n pi) p lr = tt
no-parens{TERM} (Lam pi l' pi' x oc t) p lr = ff
no-parens{TERM} (Let pi _ dtT t) p lr = ff
no-parens{TERM} (Open _ _ _ _ _) p lr = ff
no-parens{TERM} (Parens pi t pi') p lr = tt
no-parens{TERM} (Phi pi eq t t' pi') p lr = ff
no-parens{TERM} (Rho pi op on eq og t) p lr = ff
no-parens{TERM} (Sigma pi t) p lr = is-eq-op p
no-parens{TERM} (Theta pi theta t lts) p lr = ff
no-parens{TERM} (Var pi x) p lr = tt
no-parens{TERM} (Mu _ _ _ _ _ _ _ _) p lr = ff
no-parens{TERM} (Mu' _ _ _ _ _ _ _)  p lr = ff
no-parens{TYPE} (Abs pi b pi' x Tk T) p lr = is-arrow p && not-left lr
no-parens{TYPE} (Iota pi pi' x oT T) p lr = ff
no-parens{TYPE} (Lft pi pi' x t lT) p lr = ff
no-parens{TYPE} (NoSpans T pi) p lr = tt
no-parens{TYPE} (TpApp T T') p lr = is-arrow p || (is-type-level-app p && not-right lr)
no-parens{TYPE} (TpAppt T t) p lr = is-arrow p || (is-type-level-app p && not-right lr)
no-parens{TYPE} (TpArrow T a T') p lr = is-arrow p && not-left lr
no-parens{TYPE} (TpEq _ t t' _) p lr = tt
no-parens{TYPE} (TpHole pi) p lr = tt
no-parens{TYPE} (TpLambda pi pi' x Tk T) p lr = ff
no-parens{TYPE} (TpParens pi T pi') p lr = tt
no-parens{TYPE} (TpVar pi x) p lr = tt
no-parens{TYPE} (TpLet _ _ _) _ _ = ff
no-parens{KIND} (KndArrow k k') p lr = is-arrow p && not-left lr
no-parens{KIND} (KndParens pi k pi') p lr = tt
no-parens{KIND} (KndPi pi pi' x Tk k) p lr = is-arrow p && not-left lr
no-parens{KIND} (KndTpArrow T k) p lr = is-arrow p && not-left lr
no-parens{KIND} (KndVar pi x as) p lr = tt
no-parens{KIND} (Star pi) p lr = tt
no-parens{LIFTINGTYPE} (LiftArrow lT lT') p lr = is-arrow p && not-left lr
no-parens{LIFTINGTYPE} (LiftParens pi lT pi') p lr = tt
no-parens{LIFTINGTYPE} (LiftPi pi x T lT) p lr = is-arrow p && not-left lr
no-parens{LIFTINGTYPE} (LiftStar pi) p lr = tt
no-parens{LIFTINGTYPE} (LiftTpArrow T lT) p lr = is-arrow p && not-left lr
no-parens{TK} _ _ _ = tt
no-parens{QUALIF} _ _ _ = tt
no-parens{ARG} _ _ _ = tt

pattern ced-ops-drop-spine = cedille-options.options.mk-options _ _ _ _ ff _ _ ff
pattern ced-ops-conv-arr = cedille-options.options.mk-options _ _ _ _ _ _ _ ff
pattern ced-ops-conv-abs = cedille-options.options.mk-options _ _ _ _ _ _ _ tt

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
to-string-rewrite Γ ops x = , drop-spine ops Γ x


-------------------------------
strM : Set
strM = ∀ {ed} → rope → ℕ → 𝕃 tag → ctxt → maybe ⟦ ed ⟧ → expr-side → rope × ℕ × 𝕃 tag

to-stringh : {ed : exprd} → ⟦ ed ⟧ → strM

strM-Γ : (ctxt → strM) → strM
strM-Γ f s n ts Γ = f Γ s n ts Γ

infixr 4 _≫str_

_≫str_ : strM → strM → strM
(m ≫str m') s n ts Γ pe lr with m s n ts Γ pe lr
(m ≫str m') s n ts Γ pe lr | s' , n' , ts' = m' s' n' ts' Γ pe lr

strAdd : string → strM
strAdd s s' n ts Γ pe lr = s' ⊹⊹ [[ s ]] , n + string-length s , ts

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
  sₒ ⊹⊹ [[ sₙ ]] , n' , map (uncurry λ k vs → make-tag k vs n n') tsₙ ++ tsₒ

strVar : var → strM
strVar v = strM-Γ λ Γ →
  let uqv = unqual-local v -- $ unqual-all (ctxt-get-qualif Γ) v
      uqv' = if cedille-options.options.show-qualified-vars options then v else uqv in
  strAddTags uqv' (var-tags Γ (qualif-var Γ v) uqv)


-- Only necessary to unqual-local because of module parameters
strBvar : var → (class body : strM) → strM
strBvar v cm bm = strAdd (unqual-local v) ≫str cm ≫str strΓ' localScope v bm

strMetaVar : var → span-location → strM
strMetaVar x (fn , pi , pi') s n ts Γ pe lr =
  let n' = n + string-length x in
  s ⊹⊹ [[ x ]] , n' , make-loc-tag Γ fn pi pi' n n' :: ts

strEmpty : strM
strEmpty s n ts Γ pe lr = s , n , ts

{-# TERMINATING #-}
term-to-stringh : term → strM
type-to-stringh : type → strM
kind-to-stringh : kind → strM
liftingType-to-stringh : liftingType → strM
tk-to-stringh : tk → strM
ctr-to-string : ctr → strM
ctrs-to-string : ctrs → strM
case-to-string : case → strM
cases-to-string : cases → strM
caseArgs-to-string : caseArgs → strM → strM

params-to-string : params → strM
params-to-string' : strM → params → strM
file-to-string : start → strM
cmds-to-string : cmds → strM → strM
cmd-to-string : cmd → strM → strM  
optTerm-to-string : optTerm → string → string → strM
optClass-to-string : optClass → strM
optGuide-to-string : optGuide → strM
optNums-to-string : optNums → strM
optType-to-string : string → optType → strM
maybeCheckType-to-string : optType → strM
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
  parens-unless p s = if p then s else (strAdd "(" ≫str s ≫str strAdd ")")

to-stringl : {ed : exprd} → ⟦ ed ⟧ → strM
to-stringr : {ed : exprd} → ⟦ ed ⟧ → strM
to-stringl = to-stringh' left
to-stringr = to-stringh' right
to-stringh = to-stringh' neither

ctr-to-string (Ctr _ x T) = strAdd x ≫str strAdd " : " ≫str to-stringh T

ctrs-to-string [] = strEmpty
ctrs-to-string (c :: []) = ctr-to-string c
ctrs-to-string (c :: cs) =
  ctr-to-string c ≫str
  strAdd " | "  ≫str
  ctrs-to-string cs
{-
caseArgs-drop-params : params → caseArgs → caseArgs
caseArgs-drop-params (Decl _ _ NotErased x (Tkt T) _ :: ps) (CaseTermArg _ NotErased ignored-var :: as) =
  caseArgs-drop-params ps as
caseArgs-drop-params (Decl _ _ Erased x (Tkt T) _ :: ps) (CaseTermArg _ Erased ignored-var :: as) =
  caseArgs-drop-params ps as
caseArgs-drop-params (Decl _ _ _ x (Tkk k) _ :: ps) (CaseTypeArg _ ignored-var :: as) =
  caseArgs-drop-params ps as
caseArgs-drop-params (_ :: ps) as = caseArgs-drop-params ps as
caseArgs-drop-params [] as = as
-}
case-to-string (Case _ x as t) =
  strM-Γ λ Γ →
  let as-f = λ x as → strVar x ≫str caseArgs-to-string as (strAdd " ➔ " ≫str to-stringr t) in
  case (env-lookup Γ x , options) of uncurry λ where
    (just (ctr-def mps T _ _ _ , _ , _)) ced-ops-drop-spine →
          as-f (unqual-all (ctxt-get-qualif Γ) x) as
            -- $ maybe-else' mps as $ flip caseArgs-drop-params as
    _ _ → as-f x as

cases-to-string [] = strEmpty
cases-to-string (m :: []) = case-to-string m
cases-to-string (m :: ms) = case-to-string m ≫str strAdd " | " ≫str cases-to-string ms

caseArgs-to-string [] m = m
caseArgs-to-string (CaseTermArg pi me x :: as) m = strAdd (" " ^ maybeErased-to-string me) ≫str strBvar x strEmpty (caseArgs-to-string as m)
caseArgs-to-string (CaseTypeArg pi x :: as) m = strAdd " · " ≫str strBvar x strEmpty (caseArgs-to-string as m)
  
tk-to-stringh (Tkt T) = to-stringh T
tk-to-stringh (Tkk k) = to-stringh k

private
  let-lbrack-to-string : forceErased → string
  let-lbrack-to-string tt = "{ "
  let-lbrack-to-string ff = "[ "

  let-rbrack-to-string : forceErased → string
  let-rbrack-to-string tt = " } - "
  let-rbrack-to-string ff = " ] - "

term-to-stringh (App t me t') = to-stringl t ≫str strAdd (" " ^ maybeErased-to-string me) ≫str to-stringr t'
term-to-stringh (AppTp t T) = to-stringl t ≫str strAdd " · " ≫str to-stringr T
term-to-stringh (Beta pi ot ot') = strAdd "β" ≫str optTerm-to-string ot " < " " >" ≫str optTerm-to-string ot' " { " " }"
term-to-stringh (Chi pi mT t) = strAdd "χ" ≫str optType-to-string " " mT ≫str strAdd " - " ≫str to-stringr t
term-to-stringh (Delta pi mT t) = strAdd "δ" ≫str optType-to-string " " mT ≫str strAdd " - " ≫str to-stringr t
term-to-stringh (Epsilon pi lr m t) = strAdd "ε" ≫str strAdd (leftRight-to-string lr) ≫str strAdd (maybeMinus-to-string m) ≫str to-stringh t
term-to-stringh (Hole pi) = strM-Γ λ Γ → strAddTags "●" (var-loc-tag Γ (split-var pi) "●")
term-to-stringh (IotaPair pi t t' og pi') = strAdd "[ " ≫str to-stringh t ≫str strAdd " , " ≫str to-stringh t' ≫str optGuide-to-string og ≫str strAdd " ]"
term-to-stringh (IotaProj t n pi) = to-stringh t ≫str strAdd ("." ^ n)
term-to-stringh (Lam pi l pi' x oc t) = strAdd (lam-to-string l) ≫str strAdd " " ≫str strBvar x (optClass-to-string oc) (strAdd " . " ≫str to-stringr t)
term-to-stringh (Let pi fe dtT t) with dtT
...| DefTerm pi' x m t' = strAdd (let-lbrack-to-string fe) ≫str strBvar x (maybeCheckType-to-string m
  ≫str strAdd " = " ≫str to-stringh t' ≫str strAdd (let-rbrack-to-string fe)) (to-stringh t)
...| DefType pi' x k t' = strAdd "[ " ≫str strBvar x (strAdd " : " ≫str to-stringh k ≫str strAdd " = " ≫str to-stringh t' ≫str strAdd " ] - ") (to-stringh t)
--term-to-stringh (Open elab-hide-key o pi' x t) = term-to-stringh t
term-to-stringh (Open pi o pi' x t) = strAdd (if o iff OpacTrans then "open " else "close ") ≫str strVar x ≫str strAdd " - " ≫str to-stringh t
term-to-stringh (Parens pi t pi') = to-stringh t
term-to-stringh (Phi pi eq t t' pi') = strAdd "φ " ≫str to-stringl eq ≫str strAdd " - " ≫str to-stringh t ≫str strAdd " { " ≫str to-stringr t' ≫str strAdd " }"
term-to-stringh (Rho pi op on eq og t) = strAdd "ρ" ≫str strAdd (optPlus-to-string op) ≫str optNums-to-string on ≫str strAdd " " ≫str to-stringl eq ≫str optGuide-to-string og ≫str strAdd " - " ≫str to-stringr t
term-to-stringh (Sigma pi t) = strAdd "ς " ≫str to-stringh t
term-to-stringh (Theta pi theta t lts) = theta-to-string theta ≫str to-stringh t ≫str lterms-to-string lts
term-to-stringh (Var pi x) = strVar x
term-to-stringh (Mu pi pi' x t ot pi'' cs pi''') = strAdd "μ " ≫str strBvar x (strAdd " . " ≫str to-stringl t ≫str optType-to-string " @ " ot) (strAdd " { " ≫str cases-to-string cs ≫str strAdd " }")
term-to-stringh (Mu' pi ot t oT pi' cs pi'') = strAdd "μ' " ≫str optTerm-to-string ot " < " " > " ≫str to-stringl t ≫str optType-to-string " @ " oT ≫str strAdd " { " ≫str cases-to-string cs ≫str strAdd " }"

type-to-stringh (Abs pi b pi' x Tk T) = strAdd (binder-to-string b ^ " ") ≫str strBvar x (strAdd " : " ≫str tk-to-stringh Tk ≫str strAdd " . ") (to-stringh T)
type-to-stringh (Iota pi pi' x T T') = strAdd "ι " ≫str strBvar x (strAdd " : " ≫str to-stringh T ≫str strAdd " . ") (to-stringh T')
type-to-stringh (Lft pi pi' x t lT) = strAdd "↑ " ≫str strBvar x (strAdd " . ") (to-stringh t) ≫str strAdd " : " ≫str to-stringh lT
type-to-stringh (NoSpans T pi) = to-string-ed T
type-to-stringh (TpApp T T') = to-stringl T ≫str strAdd " · " ≫str to-stringr T'
type-to-stringh (TpAppt T t) = to-stringl T ≫str strAdd " " ≫str to-stringr t
type-to-stringh (TpArrow T a T') = to-stringl T ≫str strAdd (arrowtype-to-string a) ≫str to-stringr T'
type-to-stringh (TpEq _ t t' _) = strAdd "{ " ≫str to-stringh (erase-term t) ≫str strAdd " ≃ " ≫str to-stringh (erase-term t') ≫str strAdd " }"
type-to-stringh (TpHole pi) = strM-Γ λ Γ → strAddTags "●" (var-loc-tag Γ (split-var pi) "●")
type-to-stringh (TpLambda pi pi' x Tk T) = strAdd "λ " ≫str strBvar x (strAdd " : " ≫str tk-to-stringh Tk ≫str strAdd " . ") (to-stringr T)
type-to-stringh (TpParens pi T pi') = to-stringh T
type-to-stringh (TpVar pi x) = strVar x
type-to-stringh (TpLet pi dtT t) with dtT
...| DefTerm pi' x m t' = strAdd "[ " ≫str strBvar x (maybeCheckType-to-string m ≫str strAdd " = " ≫str to-stringh t' ≫str strAdd " ] - ") (to-stringh t)
...| DefType pi' x k t' = strAdd "[ " ≫str strBvar x (strAdd " : " ≫str to-stringh k ≫str strAdd " = " ≫str to-stringh t' ≫str strAdd " ] - ") (to-stringh t)

kind-to-stringh (KndArrow k k') = to-stringl k ≫str strAdd " ➔ " ≫str to-stringr k'
kind-to-stringh (KndParens pi k pi') = to-stringh k
kind-to-stringh (KndPi pi pi' x Tk k) = strAdd "Π " ≫str strBvar x (strAdd " : " ≫str tk-to-stringh Tk ≫str strAdd " . ") (to-stringh k)
kind-to-stringh (KndTpArrow T k) = to-stringl T ≫str strAdd " ➔ " ≫str to-stringr k
kind-to-stringh (KndVar pi x as) = strVar x ≫str args-to-string as
kind-to-stringh (Star pi) = strAdd "★"

liftingType-to-stringh (LiftArrow lT lT') = to-stringl lT ≫str strAdd " ➔↑ " ≫str to-stringr lT'
liftingType-to-stringh (LiftParens pi lT pi') = strAdd "(" ≫str to-string-ed lT ≫str strAdd ")"
liftingType-to-stringh (LiftPi pi x T lT) = strAdd "Π↑ " ≫str strBvar x (strAdd " : " ≫str to-stringh T ≫str strAdd " . ") (to-stringh lT)
liftingType-to-stringh (LiftStar pi) = strAdd "☆"
liftingType-to-stringh (LiftTpArrow T lT) = to-stringl T ≫str strAdd " ➔↑ " ≫str to-stringr lT
optTerm-to-string NoTerm c1 c2 = strEmpty
optTerm-to-string (SomeTerm t _) c1 c2 = strAdd c1 ≫str to-stringh (erase-term t) ≫str strAdd c2
optClass-to-string NoClass = strEmpty
optClass-to-string (SomeClass Tk) = strAdd " : " ≫str tk-to-stringh Tk
optGuide-to-string NoGuide = strEmpty
optGuide-to-string (Guide pi v T) = strAdd " @ " ≫str strBvar v (strAdd " . ") (to-stringh T)
optType-to-string pfx NoType = strEmpty
optType-to-string pfx (SomeType T) = strAdd pfx ≫str to-stringh T
maybeCheckType-to-string NoType = strEmpty
maybeCheckType-to-string (SomeType T) = strAdd " : " ≫str to-stringh T
lterms-to-string (Lterm m t :: ts) = strAdd (" " ^ maybeErased-to-string m) ≫str to-stringh t ≫str lterms-to-string ts
lterms-to-string [] = strEmpty
arg-to-string (TermArg me t) = strAdd (maybeErased-to-string me) ≫str to-stringh t
arg-to-string (TypeArg T) = strAdd "· " ≫str to-stringh T
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
arrowtype-to-string NotErased = " ➔ "
arrowtype-to-string Erased = " ➾ "
maybeMinus-to-string EpsHnf = ""
maybeMinus-to-string EpsHanf = "-"
optPlus-to-string RhoPlain = ""
optPlus-to-string RhoPlus = "+"
optPublic-to-string NotPublic = ""
optPublic-to-string IsPublic = "public "
optAs-to-string NoOptAs = strEmpty
optAs-to-string (SomeOptAs _ x) = strAdd " as " ≫str strAdd x

braceL : maybeErased → string
braceL me = if me then "{" else "("

braceR : maybeErased → string
braceR me = if me then "}" else ")"

param-to-string : decl → strM → strM
param-to-string (Decl _ pi me v atk _) f =
  strAdd (braceL me) ≫str
  strAdd (unqual-local v) ≫str
  strAdd " : " ≫str
  tk-to-stringh atk ≫str
  strAdd (braceR me) ≫str
  strΓ' localScope v f
params-to-string' f [] = f
params-to-string' f (p :: []) = param-to-string p f
params-to-string' f (p :: ps) = param-to-string p (strAdd " " ≫str params-to-string' f ps)

params-to-string = params-to-string' strEmpty

file-to-string (File is _ _ mn ps cs _) =
   cmds-to-string (imps-to-cmds is)
  (strAdd "module " ≫str
   strAdd mn ≫str
   strAdd " " ≫str
   params-to-string'
  (strAdd "." ≫str strAdd "\n" ≫str
   cmds-to-string cs strEmpty) ps)

cmds-to-string [] f = f
cmds-to-string (c :: cs) f =
   strAdd "\n" ≫str
   cmd-to-string c
  (strAdd "\n" ≫str
   cmds-to-string cs f)
  
cmd-to-string (DefTermOrType op (DefTerm pi x mcT t) _) f =
  strM-Γ λ Γ →
  let ps = ctxt-get-current-params Γ
      ps' = if pi =string elab-hide-key then [] else ps in
  strAdd (opacity-to-string op) ≫str
  strAdd x ≫str
  maybeCheckType-to-string (case mcT of λ where
     NoType → NoType
     (SomeType T) → SomeType (abs-expand-type ps' T)) ≫str
  strAdd " = " ≫str
  to-stringh (lam-expand-term ps' t) ≫str
  strAdd " ." ≫str
  strΓ' globalScope x f
cmd-to-string (DefTermOrType op (DefType pi x k T) _) f =
  strM-Γ λ Γ →
  let ps = ctxt-get-current-params Γ
      ps' = if pi =string elab-hide-key then [] else ps in
  strAdd (opacity-to-string op) ≫str
  strAdd x ≫str
  strAdd " : " ≫str
  to-stringh (abs-expand-kind ps' k) ≫str
  strAdd " = " ≫str
  to-stringh (lam-expand-type ps' T) ≫str
  strAdd " ." ≫str
  strΓ' globalScope x f
cmd-to-string (DefKind pi x ps k _) f =
  strM-Γ λ Γ →
  let ps' = ctxt-get-current-params Γ in
  strAdd x ≫str
  params-to-string (ps' ++ ps) ≫str
  strAdd " = " ≫str
  to-stringh k ≫str
  strAdd " ." ≫str
  strΓ' globalScope x f
cmd-to-string (ImportCmd (Import _ op _ fn oa as _)) f =
  strAdd "import " ≫str
  strAdd (optPublic-to-string op) ≫str
  strAdd fn ≫str
  optAs-to-string oa ≫str
  args-to-string as ≫str
  strAdd " ." ≫str
  f
cmd-to-string (DefDatatype (Datatype pi pi' x ps k cs ) pi'') f =
  strAdd "data " ≫str
  strAdd x ≫str
  strAdd " " ≫str  
  params-to-string ps ≫str
  strAdd " : " ≫str    
  kind-to-stringh k ≫str
  strAdd " = " ≫str
  ctrs-to-string cs ≫str
  strΓ' globalScope x f

strRun : ctxt → strM → rope
strRun Γ m = fst (m {TERM} [[]] 0 [] Γ nothing neither)

strRunTag : (name : string) → ctxt → strM → tagged-val
strRunTag name Γ m with m {TERM} [[]] 0 [] Γ nothing neither
...| s , n , ts = name , s , ts

to-string-tag : {ed : exprd} → string → ctxt → ⟦ ed ⟧ → tagged-val
to-string-tag name Γ t = strRunTag name Γ
  (to-stringh
    (if cedille-options.options.erase-types options
       then erase t
       else t))

to-string : {ed : exprd} → ctxt → ⟦ ed ⟧ → rope
to-string Γ t = strRun Γ (to-stringh t)


tk-to-string : ctxt → tk → rope
tk-to-string Γ atk = strRun Γ (tk-to-stringh atk)

params-to-string-tag : string → ctxt → params → tagged-val
params-to-string-tag name Γ ps = strRunTag name Γ (params-to-string ps)

