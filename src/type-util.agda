module type-util where
open import lib
open import cedille-types
open import general-util
open import syntax-util

data tty : Set where
  tterm : term → tty
  ttype : type → tty

tty-to-arg : erased? → tty → arg
tty-to-arg me (tterm t) = TmArg me t
tty-to-arg me (ttype T) = TpArg T

ttys-to-args : erased? → 𝕃 tty → args
ttys-to-args = map ∘ tty-to-arg

ttys-to-args-for-params : (keep-extra : maybe erased?) → params → 𝕃 tty → args
ttys-to-args-for-params b ((Param me _ _) :: ps) ((tterm t) :: as) =
  TmArg me t :: ttys-to-args-for-params b ps as
ttys-to-args-for-params b (_ :: ps) ((ttype T) :: as) =
  TpArg T :: ttys-to-args-for-params b ps as
ttys-to-args-for-params nothing _ _ = []
ttys-to-args-for-params (just me) _ as = ttys-to-args me as

arg-to-tty : arg → tty
arg-to-tty (TmArg me t) = tterm t
arg-to-tty (TpArg T) = ttype T

args-to-ttys : args → 𝕃 tty
args-to-ttys = map arg-to-tty

params-to-args : params → args
params-to-args = map λ where
  (Param me v (Tkt T)) → TmArg me (Var v)
  (Param me v (Tkk k)) → TpArg (TpVar v)

decompose-lams : term → (𝕃 var) × term
decompose-lams (Lam _ x _ t) with decompose-lams t
decompose-lams (Lam _ x _ t) | vs , body = (x :: vs) , body
decompose-lams t = [] , t

decompose-apps : term → term × args
decompose-apps = h [] where
  h : args → term → term × args
  h acc (App t me t') = h (TmArg me t' :: acc) t
  h acc (AppTp t T) = h (TpArg T :: acc) t
  h acc t = t , acc

decompose-tpapps : type → type × 𝕃 tty
decompose-tpapps = h [] where
  h : 𝕃 tty → type → type × 𝕃 tty
  h acc (TpApp T T') = h (ttype T' :: acc) T
  h acc (TpAppt T t) = h (tterm t :: acc) T
  h acc T = T , acc

decompose-var-headed : term → maybe (var × args)
decompose-var-headed t with decompose-apps t
decompose-var-headed t | Var x , as = just (x , as)
decompose-var-headed t | _ = nothing

recompose-apps : args → term → term
recompose-apps = flip $ foldl λ {(TmArg me t') t → App t me t'; (TpArg T) t → AppTp t T}

recompose-tpapps : 𝕃 tty → type → type
recompose-tpapps = flip $ foldl λ {(ttype T') T → TpApp T T'; (tterm t) T → TpAppt T t}

apps-term : term → args → term
apps-term = foldl λ {(TmArg me t) x → App x me t; (TpArg T) x → AppTp x T}

apps-type : type → args → type
apps-type = foldl λ {(TmArg _ t) x → TpAppt x t; (TpArg T) x → TpApp x T}

lam-expand-term : params → term → term
lam-expand-term = flip $ foldr λ where
  (Param me x atk) → Lam me x (just atk)

lam-expand-type : params → type → type
lam-expand-type = flip $ foldr λ where
  (Param me x atk) → TpLam x atk

abs-expand-type : params → type → type
abs-expand-type = flip $ foldr λ where
  (Param me x atk) → TpAbs me x atk

abs-expand-kind : params → kind → kind
abs-expand-kind = flip $ foldr λ where
  (Param me x atk) → KdAbs x atk

case-args-to-lams : case-args → term → term
case-args-to-lams = flip $ foldr λ where
  (CaseArg CaseArgTm x) → Lam ff x nothing
  (CaseArg _ x) → Lam tt x nothing

expand-case : case → term
expand-case (Case x xs t) = case-args-to-lams xs t

is-eq-tp? : {ed : exprd} → ⟦ ed ⟧ → maybe (term × term)
is-eq-tp? {TYPE} (TpEq t₁ t₂) = just $ t₁ , t₂
is-eq-tp? _ = nothing

arg-set-erased : erased? → arg → arg
arg-set-erased me (TmArg _ t) = TmArg me t
arg-set-erased me (TpArg T) = TpArg T


is-var : tty → maybe var
is-var (tterm (Var x)) = just x
is-var (ttype (TpVar x)) = just x
is-var _ = nothing

is-var-unqual : tty → maybe var
is-var-unqual = maybe-map (λ x → maybe-else (unqual-local x) id (var-suffix x)) ∘ is-var

unerased-arrows : type → ℕ
unerased-arrows (TpAbs ff x atk T) = suc (unerased-arrows T)
unerased-arrows _ = zero
