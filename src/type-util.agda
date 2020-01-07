module type-util where
open import cedille-types
open import general-util
open import syntax-util

tmtp-to-arg : erased? → tmtp → arg
tmtp-to-arg ff (inj₁ t) = Arg t
tmtp-to-arg me = ArgE

tmtps-to-args : erased? → 𝕃 tmtp → args
tmtps-to-args = map ∘ tmtp-to-arg

tmtps-to-args-for-params : (keep-extra : maybe erased?) → params → 𝕃 tmtp → args
tmtps-to-args-for-params b (ParamTm _ _ :: ps) (inj₁ t :: as) =
   Arg t :: tmtps-to-args-for-params b ps as
tmtps-to-args-for-params b (_ :: ps) (tT :: as) =
  ArgE tT :: tmtps-to-args-for-params b ps as
tmtps-to-args-for-params nothing _ _ = []
tmtps-to-args-for-params (just me) _ as = tmtps-to-args me as

arg-to-tmtp : arg → tmtp
arg-to-tmtp a = a >>= id

args-to-tmtps : args → 𝕃 tmtp
args-to-tmtps = map arg-to-tmtp

params-to-args : params → args
params-to-args = map λ where
  (ParamTm v _) → Arg (Var v)
  (ParamEr v _) → ArgEr (Var v)
  (ParamTp v _) → ArgTp (TpVar v)

decompose-lams : term → (𝕃 var) × term
decompose-lams (Lam _ x _ t) with decompose-lams t
decompose-lams (Lam _ x _ t) | vs , body = (x :: vs) , body
decompose-lams t = [] , t

decompose-apps : term → term × args
decompose-apps = h [] where
  h : args → term → term × args
  h acc (App t t') = h (Arg t' :: acc) t
  h acc (AppE t tT) = h (ArgE tT :: acc) t
  h acc t = t , acc

decompose-tpapps : type → type × 𝕃 tmtp
decompose-tpapps = h [] where
  h : 𝕃 tmtp → type → type × 𝕃 tmtp
  h acc (TpApp T tT) = h (tT :: acc) T
  h acc T = T , acc

decompose-var-headed : term → maybe (var × args)
decompose-var-headed t with decompose-apps t
decompose-var-headed t | Var x , as = just (x , as)
decompose-var-headed t | _ = nothing

decompose-tpvar-headed : type → maybe (var × 𝕃 tmtp)
decompose-tpvar-headed T with decompose-tpapps T
decompose-tpvar-headed T | TpVar x , as = just (x , as)
decompose-tpvar-headed T | _ = nothing

recompose-apps : args → term → term
recompose-apps = flip $ foldl λ a t → either-else' a (App t) (AppE t)

recompose-tpapps : 𝕃 tmtp → type → type
recompose-tpapps = flip $ foldl $ flip TpApp

apps-term : term → args → term
apps-term = flip recompose-apps

apps-type : type → args → type
apps-type = foldl $ flip TpApp ∘ arg-to-tmtp

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
  (CaseArg me x atk) → Lam me x atk

expand-case : case → term
expand-case (Case x xs t T) = case-args-to-lams xs t

is-eq-tp? : {ed : exprd} → ⟦ ed ⟧ → maybe (term × term)
is-eq-tp? {TYPE} (TpEq t₁ t₂) = just $ t₁ , t₂
is-eq-tp? _ = nothing

arg-set-erased : erased? → arg → arg
arg-set-erased tt (Arg t) = ArgEr t
arg-set-erased ff (ArgEr t) = Arg t
arg-set-erased e a = a


is-var : tmtp → maybe var
is-var (Ttm (Var x)) = just x
is-var (Ttp (TpVar x)) = just x
is-var _ = nothing

arg-var : arg → maybe var
arg-var = either-else (is-var ∘ Ttm) is-var

is-var-unqual : tmtp → maybe var
is-var-unqual = maybe-map (λ x → maybe-else (unqual-local x) id (var-suffix x)) ∘ is-var

unerased-arrows : type → ℕ
unerased-arrows (TpAbs ff x atk T) = suc (unerased-arrows T)
unerased-arrows (TpAbs tt x atk T) = unerased-arrows T
unerased-arrows _ = zero

lterms-to-term : theta → ex-tm → 𝕃 lterm → ex-tm
lterms-to-term AbstractEq t [] = ExApp t Erased (ExBeta (term-end-pos t) nothing nothing)
lterms-to-term _ t [] = t
lterms-to-term θ t (Lterm e t' :: ls) = lterms-to-term θ (ExApp t e t') ls

is-hole : ∀ {ed} → ⟦ ed ⟧ → 𝔹
is-hole {TERM} (Hole pi) = tt
is-hole {TYPE} (TpHole pi) = tt
is-hole {KIND} (KdHole pi) = tt
is-hole _ = ff


data datatype : Set where
  Data : var → params → indices → ctrs → datatype


tk-erased : tpkd → erased? → erased?
tk-erased (Tkk _) me = Erased
tk-erased (Tkt _) me = me

params-set-erased : erased? → params → params
params-set-erased me = map λ where
  (Param me' x atk) → Param me x atk

args-set-erased : erased? → args → args
args-set-erased = map ∘ arg-set-erased

indices-to-params : indices → params
indices-to-params = map λ where
  (Index x tk) → Param ff x tk

params-to-indices : params → indices
params-to-indices = map λ where
  (Param me x tk) → Index x tk

indices-to-tmtps : indices → 𝕃 tmtp
indices-to-tmtps = map λ where
  (Index x (Tkt T)) → Ttm (Var x)
  (Index x (Tkk k)) → Ttp (TpVar x)

indices-to-kind : indices → kind → kind
indices-to-kind = flip $ foldr λ {(Index x atk) → KdAbs x atk}

params-to-kind : params → kind → kind
params-to-kind = flip $ foldr λ {(Param me x atk) → KdAbs x atk}

indices-to-tplams : indices → (body : type) → type
indices-to-tplams = flip $ foldr λ where
  (Index x atk) → TpLam x atk

params-to-tplams : params → (body : type) → type
params-to-tplams = flip $ foldr λ where
  (Param me x atk) → TpLam x atk

indices-to-alls : indices → (body : type) → type
indices-to-alls = flip $ foldr λ where
  (Index x atk) → TpAbs Erased x atk

params-to-alls : params → (body : type) → type
params-to-alls = flip $ foldr λ where
  (Param me x atk) → TpAbs (tk-erased atk me) x atk

indices-to-lams : indices → (body : term) → term
indices-to-lams = flip $ foldr λ where
  (Index x atk) → Lam Erased x (just atk)

params-to-lams : params → (body : term) → term
params-to-lams = flip $ foldr λ where
  (Param me x atk) → Lam (tk-erased atk me) x (just atk)

indices-to-apps : indices → (body : term) → term
indices-to-apps = flip $ foldl λ where
  (Index x (Tkt T)) t → AppEr t (Var x)
  (Index x (Tkk k)) t → AppTp t (TpVar x)

params-to-apps : params → (body : term) → term
params-to-apps = recompose-apps ∘ params-to-args

indices-to-tpapps : indices → (body : type) → type
indices-to-tpapps = flip $ foldl λ where
  (Index x (Tkt _)) T → TpAppTm T (Var x)
  (Index x (Tkk _)) T → TpAppTp T (TpVar x)

params-to-tpapps : params → (body : type) → type
params-to-tpapps = flip apps-type ∘ params-to-args

params-to-case-args : params → case-args
params-to-case-args = map λ where
  (Param me x tk) → CaseArg me x (just tk)

ctrs-to-lams : ctrs → term → term
ctrs-to-lams = flip $ foldr λ {(Ctr x T) → Lam NotErased x (just (Tkt T))}

indices-to-args : indices → args
indices-to-args = λ is → map (λ {(Index x atk) → either-else' atk (λ _ → ArgEr (Var x)) (λ _ → ArgTp (TpVar x))}) is
