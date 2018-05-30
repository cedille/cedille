import cedille-options

module to-string (options : cedille-options.options) where

open import lib
open import cedille-types
open import syntax-util
open import ctxt
open import rename
open import general-util

drop-mod-args : ctxt → maybeErased → spineApp → spineApp
drop-mod-args Γ me ((pi , v) , as) = (pi , qv) , if (v =string qv)
  then as else maybe-else as
  (λ n → reverse (drop n (reverse as))) mn
  where
  qv = unqual-all (ctxt-get-qualif Γ) v
  mn = ctxt-qualif-args-length Γ me qv

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
no-parens {_} {TERM} _ (Parens pi t pi') lr = tt
no-parens {_} {TYPE} _ (TpParens pi T pi') lr = tt
no-parens {_} {KIND} _ (KndParens pi k pi') lr = tt
no-parens {_} {LIFTINGTYPE} _ (LiftParens pi lT pi') lr = tt
no-parens {_} {TYPE} _ (TpEq _ t t' _) lr = tt
no-parens {_} {TERM} _ (Beta pi ot ot') lr = tt
no-parens {_} {TERM} _ (Phi pi eq t t' pi') right = tt
no-parens {_} {TERM} _ (Phi pi eq t t' pi') neither = tt
no-parens {_} {TERM} _ (Let _ _ _) _ = tt
no-parens {_} {TERM} _ (Rho _ _ _ _ _ _) right = tt
no-parens {_} {TERM} _ (Chi _ _ _) right = tt
no-parens {_} {TERM} _ (Lam _ _ _ _ _ _) right = tt
no-parens {_} {TYPE} _ (TpLambda _ _ _ _ _) right = tt
no-parens{TERM} (App t me t') p lr = is-abs p || (is-arrow p || is-app p) && not-right lr
no-parens{TERM} (AppTp t T) p lr = is-abs p || (is-arrow p || is-app p) && not-right lr
no-parens{TERM} (Beta pi ot ot') p lr = tt
no-parens{TERM} (Chi pi mT t) p lr = ff
no-parens{TERM} (Delta pi mT t) p lr = ff
no-parens{TERM} (Epsilon pi lr' m t) p lr = tt
no-parens{TERM} (Hole pi) p lr = tt
no-parens{TERM} (IotaPair pi t t' og pi') p lr = tt
no-parens{TERM} (IotaProj t n pi) p lr = tt
no-parens{TERM} (Lam pi l' pi' x oc t) p lr = is-abs p
no-parens{TERM} (Let pi dtT t) p lr = tt
no-parens{TERM} (Parens pi t pi') p lr = tt
no-parens{TERM} (Phi pi eq t t' pi') p lr = ff
no-parens{TERM} (Rho pi op on eq og t) p lr = ff
no-parens{TERM} (Sigma pi t) p lr = is-eq-op p
no-parens{TERM} (Theta pi theta t lts) p lr = ff
no-parens{TERM} (Var pi x) p lr = tt
no-parens{TYPE} (Abs pi b pi' x Tk T) p lr = (is-abs p || is-arrow p) && not-left lr
no-parens{TYPE} (Iota pi pi' x oT T) p lr = is-abs p
no-parens{TYPE} (Lft pi pi' x t lT) p lr = ff
no-parens{TYPE} (NoSpans T pi) p lr = tt
no-parens{TYPE} (TpApp T T') p lr = is-abs p || is-arrow p || is-app p && not-right lr
no-parens{TYPE} (TpAppt T t) p lr = is-abs p || is-arrow p || is-app p && not-right lr
no-parens{TYPE} (TpArrow T a T') p lr = (is-abs p || is-arrow p) && not-left lr
no-parens{TYPE} (TpEq _ t t' _) p lr = tt
no-parens{TYPE} (TpHole pi) p lr = tt
no-parens{TYPE} (TpLambda pi pi' x Tk T) p lr = is-abs p
no-parens{TYPE} (TpParens pi T pi') p lr = tt
no-parens{TYPE} (TpVar pi x) p lr = tt
no-parens{KIND} (KndArrow k k') p lr = (is-abs p || is-arrow p) && not-left lr
no-parens{KIND} (KndParens pi k pi') p lr = tt
no-parens{KIND} (KndPi pi pi' x Tk k) p lr = (is-abs p || is-arrow p) && not-left lr
no-parens{KIND} (KndTpArrow T k) p lr = (is-abs p || is-arrow p) && not-left lr
no-parens{KIND} (KndVar pi x as) p lr = tt
no-parens{KIND} (Star pi) p lr = tt
no-parens{LIFTINGTYPE} (LiftArrow lT lT') p lr = (is-abs p || is-arrow p) && not-left lr
no-parens{LIFTINGTYPE} (LiftParens pi lT pi') p lr = tt
no-parens{LIFTINGTYPE} (LiftPi pi x T lT) p lr = (is-abs p || is-arrow p) && not-left lr
no-parens{LIFTINGTYPE} (LiftStar pi) p lr = tt
no-parens{LIFTINGTYPE} (LiftTpArrow T lT) p lr = (is-abs p || is-arrow p) && not-left lr
no-parens{TK} _ _ _ = tt
no-parens{QUALIF} _ _ _ = tt
no-parens{ARG} _ _ _ = tt


-------------------------------
strM : Set
strM = {ed : exprd} → rope → ℕ → 𝕃 tag → ctxt → maybe ⟦ ed ⟧ → expr-side →
  rope × ℕ × 𝕃 tag

to-stringh : {ed : exprd} → ⟦ ed ⟧ → strM

strM-Γ : (ctxt → strM) → strM
strM-Γ f s n ts Γ = f Γ s n ts Γ
strM-n : (ℕ → strM) → strM
strM-n f s n = f n s n
strM-p : ({ed : exprd} → maybe ⟦ ed ⟧ → strM) → strM
strM-p f s n ts Γ pe = f pe s n ts Γ pe

infixr 4 _≫str_

_≫str_ : strM → strM → strM
(m ≫str m') s n ts Γ pe lr with m s n ts Γ pe lr
(m ≫str m') s n ts Γ pe lr | s' , n' , ts' = m' s' n' ts' Γ pe lr

strAdd : string → strM
strAdd s s' n ts Γ pe lr = s' ⊹⊹ [[ s ]] , n + (string-length s) , ts

strΓ' : defScope → var → posinfo → strM → strM
strΓ' ds v pi m s n ts Γ@(mk-ctxt (fn , mn , ps , q) syms i symb-occs) pe =
  m s n ts
    (mk-ctxt (fn , mn , ps , (trie-insert q v (v' , ArgsNil))) syms (trie-insert i v' (var-decl , ("missing" , "missing"))) symb-occs)
    pe
  where v' = if ds iff localScope then pi % v else mn # v

strΓ = strΓ' localScope

ctxt-global-var-location : ctxt → var → location
ctxt-global-var-location (mk-ctxt mod ss is os) v with trie-lookup is v
...| just (term-def _ _ _ , loc) = loc
...| just (term-udef _ _ , loc) = loc
...| just (type-def _ _ _ , loc) = loc
...| just (kind-def _ _ _ , loc) = loc
...| _ = "missing" , "missing"

var-loc-tag : ctxt → location → ℕ → ℕ → 𝕃 tag
var-loc-tag Γ ("missing" , "missing") start end = []
var-loc-tag Γ (fn , pos) start end = [ make-tag "loc" (("fn" , [[ fn ]]) :: [ "pos" , [[ pos ]] ]) start end ]

var-tags : ctxt → qvar → var → ℕ → ℕ → 𝕃 tag
var-tags Γ qv uqv s e with qv =string (qualif-var Γ uqv)
...| tt = var-loc-tag Γ (ctxt-global-var-location Γ qv) s e
...| ff = make-tag "shadowed" [] s e :: var-loc-tag Γ (ctxt-var-location Γ qv) s e

strVar : var → strM
strVar v s n ts Γ pe lr =
  let uqv = unqual-local (unqual-all (ctxt-get-qualif Γ) v) in
  let uqv' = if cedille-options.options.show-qualified-vars options then v else uqv in
  let n' = n + (string-length uqv') in
  s ⊹⊹ [[ uqv' ]] , n' , var-tags Γ (qualif-var Γ v) uqv n n' ++ ts

strEmpty : strM
strEmpty s n ts Γ pe lr = s , n , ts

{-# TERMINATING #-}
spine-term-to-stringh : term → strM
spine-type-to-stringh : type → strM

term-to-stringh : term → strM
type-to-stringh : type → strM
kind-to-stringh : kind → strM
liftingType-to-stringh : liftingType → strM
tk-to-stringh : tk → strM

file-to-string : start → strM
cmds-to-string : cmds → strM → strM
cmd-to-string : cmd → strM → strM

params-to-string : params → strM
params-to-string' : defScope → strM → params → strM
optTerm-to-string : optTerm → string → string → strM
-- optType-to-string : optType → strM
optClass-to-string : optClass → strM
optGuide-to-string : optGuide → strM
optNums-to-string : optNums → strM
maybeAtype-to-string : maybeAtype → strM
maybeCheckType-to-string : maybeCheckType → strM
lterms-to-string : lterms → strM
arg-to-string : arg → strM
args-to-string : args → strM
binder-to-string : binder → string
maybeErased-to-string : maybeErased → string
lam-to-string : lam → string
leftRight-to-string : leftRight → string
vars-to-string : vars → strM
nums-to-string : nums → strM
theta-to-string : theta → strM
arrowtype-to-string : arrowtype → string
maybeMinus-to-string : maybeMinus → string
optPlus-to-string : optPlus → string
optPublic-to-string : optPublic → string
optAs-to-string : optAs → strM

to-string-ed : {ed : exprd} → ⟦ ed ⟧ → strM
to-string-ed{TERM} = spine-term-to-stringh
to-string-ed{TYPE} = spine-type-to-stringh
to-string-ed{KIND} = kind-to-stringh
to-string-ed{LIFTINGTYPE} = liftingType-to-stringh
to-string-ed{TK} = tk-to-stringh
to-string-ed{ARG} = arg-to-string
to-string-ed{QUALIF} q = strEmpty

to-stringh' : {ed : exprd} → expr-side → ⟦ ed ⟧ → strM
to-stringh' lr t s n ts Γ nothing lr' = to-string-ed t s n ts Γ (just t) lr
to-stringh' lr t s n ts Γ (just pe) lr' = (if no-parens t pe lr
  then to-string-ed t
  else (strAdd "(" ≫str to-string-ed t ≫str strAdd ")")) s n ts Γ (just t) lr

to-stringl : {ed : exprd} → ⟦ ed ⟧ → strM
to-stringr : {ed : exprd} → ⟦ ed ⟧ → strM
to-stringl = to-stringh' left
to-stringr = to-stringh' right
to-stringh = to-stringh' neither

tk-to-stringh (Tkt T) = to-stringh T
tk-to-stringh (Tkk k) = to-stringh k

spine-term-to-stringh t s n ts Γ pe lr = term-to-stringh t' s n ts Γ pe lr
  where
  t' = if cedille-options.options.show-qualified-vars options
    then t
    else maybe-else t (spapp-term ∘ drop-mod-args Γ Erased) (term-to-spapp t)

spine-type-to-stringh T s n ts Γ pe lr = type-to-stringh T' s n ts Γ pe lr
  where
  T' = if cedille-options.options.show-qualified-vars options
    then T
    else maybe-else T (spapp-type ∘ drop-mod-args Γ NotErased) (type-to-spapp T)

term-to-stringh (App t me t') = to-stringl t ≫str strAdd (" " ^ maybeErased-to-string me) ≫str to-stringr t'
term-to-stringh (AppTp t T) = to-stringl t ≫str strAdd " · " ≫str to-stringr T
term-to-stringh (Beta pi ot ot') = strAdd "β" ≫str optTerm-to-string ot " < " " >" ≫str optTerm-to-string ot' " { " " }"
term-to-stringh (Chi pi mT t) = strAdd "χ" ≫str maybeAtype-to-string mT ≫str strAdd " - " ≫str to-stringr t
term-to-stringh (Delta pi mT t) = strAdd "δ" ≫str maybeAtype-to-string mT ≫str strAdd " - " ≫str to-stringr t
term-to-stringh (Epsilon pi lr m t) = strAdd "ε" ≫str strAdd (leftRight-to-string lr) ≫str strAdd (maybeMinus-to-string m) ≫str to-stringh t
term-to-stringh (Hole pi) = strAdd "●"
term-to-stringh (IotaPair pi t t' og pi') = strAdd "[ " ≫str to-stringh t ≫str strAdd " , " ≫str to-stringh t' ≫str optGuide-to-string og ≫str strAdd " ]"
term-to-stringh (IotaProj t n pi) = to-stringh t ≫str strAdd ("." ^ n)
term-to-stringh (Lam pi l pi' x oc t) = strAdd (lam-to-string l ^ " " ^ x) ≫str optClass-to-string oc ≫str strAdd " . " ≫str strΓ x pi' (to-stringr t)
term-to-stringh (Let pi dtT t) with dtT
...| DefTerm pi' x m t' = strAdd ("[ " ^ x) ≫str maybeCheckType-to-string m ≫str strAdd " = " ≫str to-stringh t' ≫str strAdd " ] - " ≫str strΓ x pi' (to-stringh t)
...| DefType pi' x k t' = strAdd ("[ " ^ x) ≫str to-stringh k ≫str strAdd " = " ≫str to-stringh t' ≫str strAdd " ] - " ≫str strΓ x pi' (to-stringh t)
term-to-stringh (Parens pi t pi') = to-stringh t
term-to-stringh (Phi pi eq t t' pi') = strAdd "φ " ≫str to-stringl eq ≫str strAdd " - (" ≫str to-stringh t ≫str strAdd ") {" ≫str to-stringr t' ≫str strAdd "}"
term-to-stringh (Rho pi op on eq og t) = strAdd "ρ" ≫str strAdd (optPlus-to-string op) ≫str optNums-to-string on ≫str strAdd " " ≫str to-stringl eq ≫str optGuide-to-string og ≫str strAdd " - " ≫str to-stringr t
term-to-stringh (Sigma pi t) = strAdd "ς " ≫str to-stringh t
term-to-stringh (Theta pi theta t lts) = theta-to-string theta ≫str to-stringh t ≫str lterms-to-string lts
term-to-stringh (Var pi x) = strVar x

type-to-stringh (Abs pi b pi' x Tk T) = strAdd (binder-to-string b ^ " " ^ x ^ " : ") ≫str tk-to-stringh Tk ≫str strAdd " . " ≫str strΓ x pi' (to-stringh T)
type-to-stringh (Iota pi pi' x T T') = strAdd ("ι " ^ x) ≫str strAdd " : " ≫str to-stringh T ≫str strAdd " . " ≫str strΓ x pi' (to-stringh T')
type-to-stringh (Lft pi pi' x t lT) = strAdd ("↑ " ^ x ^ " . ") ≫str strΓ x pi' (to-stringh t ≫str strAdd " : " ≫str to-stringh lT)
type-to-stringh (NoSpans T pi) = to-string-ed T
type-to-stringh (TpApp T T') = to-stringl T ≫str strAdd " · " ≫str to-stringr T'
type-to-stringh (TpAppt T t) = to-stringl T ≫str strAdd " " ≫str to-stringr t
type-to-stringh (TpArrow T a T') = to-stringl T ≫str strAdd (arrowtype-to-string a) ≫str to-stringr T'
type-to-stringh (TpEq _ t t' _) = strAdd "{ " ≫str to-stringh t ≫str strAdd " ≃ " ≫str to-stringh t' ≫str strAdd " }"
type-to-stringh (TpHole pi) = strAdd "●"
type-to-stringh (TpLambda pi pi' x Tk T) = strAdd ("λ " ^ x ^ " : ") ≫str tk-to-stringh Tk ≫str strAdd " . " ≫str strΓ x pi' (to-stringr T)
type-to-stringh (TpParens pi T pi') = to-stringh T
type-to-stringh (TpVar pi x) = strVar x

kind-to-stringh (KndArrow k k') = to-stringl k ≫str strAdd " ➔ " ≫str to-stringr k'
kind-to-stringh (KndParens pi k pi') = to-stringh k
kind-to-stringh (KndPi pi pi' x Tk k) = strAdd ("Π " ^ x ^ " : ") ≫str tk-to-stringh Tk ≫str strAdd " . " ≫str strΓ x pi' (to-stringh k)
kind-to-stringh (KndTpArrow T k) = to-stringl T ≫str strAdd " ➔ " ≫str to-stringr k
kind-to-stringh (KndVar pi x as) = strVar x ≫str args-to-string as
kind-to-stringh (Star pi) = strAdd "★"

liftingType-to-stringh (LiftArrow lT lT') = to-stringl lT ≫str strAdd " ➔↑ " ≫str to-stringr lT'
liftingType-to-stringh (LiftParens pi lT pi') = strAdd "(" ≫str to-string-ed lT ≫str strAdd ")"
liftingType-to-stringh (LiftPi pi x T lT) = strAdd ("Π↑ " ^ x ^ " : ") ≫str to-stringh T ≫str strAdd " . " ≫str strΓ x pi (to-stringh lT)
liftingType-to-stringh (LiftStar pi) = strAdd "☆"
liftingType-to-stringh (LiftTpArrow T lT) = to-stringl T ≫str strAdd " ➔↑ " ≫str to-stringr lT
optTerm-to-string NoTerm c1 c2 = strEmpty
optTerm-to-string (SomeTerm t _) c1 c2 = strAdd c1 ≫str to-stringh t ≫str strAdd c2
-- optType-to-string NoType = strEmpty
-- optType-to-string (SomeType T) = strAdd " : " ≫str to-stringh T
optClass-to-string NoClass = strEmpty
optClass-to-string (SomeClass Tk) = strAdd " : " ≫str tk-to-stringh Tk
optGuide-to-string NoGuide = strEmpty
optGuide-to-string (Guide pi v T) = strAdd " @ " ≫str strAdd v ≫str strAdd " . " ≫str strΓ v pi (type-to-stringh T)
maybeAtype-to-string NoAtype = strEmpty
maybeAtype-to-string (Atype T) = strAdd " " ≫str to-stringh T
maybeCheckType-to-string NoCheckType = strEmpty
maybeCheckType-to-string (Type T) = strAdd " ◂ " ≫str to-stringh T
lterms-to-string (LtermsCons m t ts) = strAdd (" " ^ maybeErased-to-string m) ≫str to-stringh t ≫str lterms-to-string ts
lterms-to-string (LtermsNil _) = strEmpty
arg-to-string (TermArg t) = to-stringh t
arg-to-string (TypeArg T) = strAdd "· " ≫str to-stringh T
args-to-string (ArgsCons t ts) = strAdd " " ≫str arg-to-string t ≫str args-to-string ts
args-to-string ArgsNil = strEmpty
binder-to-string All = "∀"
binder-to-string Pi = "Π"
maybeErased-to-string Erased = "-"
maybeErased-to-string NotErased = ""
lam-to-string ErasedLambda = "Λ"
lam-to-string KeptLambda = "λ"
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
arrowtype-to-string UnerasedArrow = " ➔ "
arrowtype-to-string ErasedArrow = " ➾ "
maybeMinus-to-string EpsHnf = ""
maybeMinus-to-string EpsHanf = "-"
optPlus-to-string RhoPlain = ""
optPlus-to-string RhoPlus = "+"
optPublic-to-string NotPublic = ""
optPublic-to-string Public = "public "
optAs-to-string NoOptAs = strEmpty
optAs-to-string (SomeOptAs _ x) = strAdd " as " ≫str strAdd x

params-to-string' ds f ParamsNil = f
params-to-string' ds f (ParamsCons (Decl _ pi v atk _) ParamsNil) =
  strAdd "(" ≫str strVar v ≫str strAdd " : " ≫str tk-to-stringh atk ≫str strAdd ")" ≫str strΓ' ds v pi f
params-to-string' ds f (ParamsCons (Decl _ pi v atk _) ps) =
  strAdd "(" ≫str strVar v ≫str strAdd " : " ≫str tk-to-stringh atk ≫str strAdd ") " ≫str
  strΓ' ds v pi (params-to-string' ds f ps)

params-to-string = params-to-string' localScope strEmpty

file-to-string (File _ is _ _ mn ps cs _) =
  cmds-to-string (imps-to-cmds is) (strAdd "module " ≫str strAdd mn ≫str strAdd " " ≫str params-to-string' globalScope (strAdd ".\n" ≫str cmds-to-string cs strEmpty) ps)

cmds-to-string CmdsStart f = f
cmds-to-string (CmdsNext c cs) f = strAdd "\n" ≫str cmd-to-string c (strAdd "\n" ≫str cmds-to-string cs f)

cmd-to-string (DefTermOrType (DefTerm pi x mcT t) _) f =
  strAdd x ≫str maybeCheckType-to-string mcT ≫str strAdd " = " ≫str to-stringh t ≫str strAdd " ." ≫str strΓ' globalScope x pi f
cmd-to-string (DefTermOrType (DefType pi x k T) _) f =
  strAdd x ≫str strAdd " ◂ " ≫str to-stringh k ≫str strAdd " = " ≫str to-stringh T ≫str strAdd " ." ≫str strΓ' globalScope x pi f
cmd-to-string (DefKind pi x ps k _) f =
  strAdd x ≫str params-to-string ps ≫str strAdd " = " ≫str to-stringh k ≫str strAdd " ." ≫str strΓ' globalScope x pi f
cmd-to-string (ImportCmd (Import _ op _ fn oa as _)) f =
  strAdd "import " ≫str strAdd (optPublic-to-string op) ≫str strAdd fn ≫str optAs-to-string oa ≫str args-to-string as ≫str strAdd " ." ≫str f


strRun : ctxt → strM → rope
strRun Γ m = fst (m {TERM} [[]] 0 [] Γ nothing neither)

strRunTag : (name : string) → ctxt → strM → tagged-val
strRunTag name Γ m with m {TERM} [[]] 0 [] Γ nothing neither
...| s , n , ts = name , s , ts

to-string-tag : {ed : exprd} → string → ctxt → ⟦ ed ⟧ → tagged-val
to-string-tag name Γ t = strRunTag name Γ (to-stringh' neither t)

to-string : {ed : exprd} → ctxt → ⟦ ed ⟧ → rope
to-string Γ t = strRun Γ (to-stringh' neither t)


tk-to-string : ctxt → tk → rope
tk-to-string Γ atk = strRun Γ (tk-to-stringh atk)

params-to-string-tag : string → ctxt → params → tagged-val
params-to-string-tag name Γ ps = strRunTag name Γ (params-to-string ps)
