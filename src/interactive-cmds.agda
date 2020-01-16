import cedille-options

module interactive-cmds (options : cedille-options.options) where

open import functions
open import cedille-types
open import conversion
open import constants
open import ctxt
open import general-util
open import spans options {Id}
open import subst
open import syntax-util
open import type-util
open import to-string options
open import toplevel-state options {IO}
open import untyped-spans options {Id}
open import parser
open import resugar
open import rewriting
open import rename
open import classify options {Id} (λ _ → return triv)
import spans options {IO} as io-spans
open import datatype-util
open import free-vars
open import json

private

  elab-typed-err : ∀ {ed} → ctxt → ⟦ ed ⟧' → ⟦ ed ⟧ × 𝔹
  elab-typed-err {TERM} Γ t =
    map-snd spans-have-error $ map-fst fst $ id-out $ check-term Γ t nothing empty-spans
  elab-typed-err {TYPE} Γ T =
    map-snd spans-have-error $ map-fst fst $ id-out $ check-type Γ T nothing empty-spans
  elab-typed-err {KIND} Γ k =
    map-snd spans-have-error $ id-out $ check-kind Γ k empty-spans

  elab-typed : ∀ {ed} → ctxt → ⟦ ed ⟧' → ⟦ ed ⟧
  elab-typed Γ = fst ∘ elab-typed-err Γ
  
  elab-untyped : ∀ {ed} → ctxt → ⟦ ed ⟧' → ⟦ ed ⟧
  elab-untyped {TERM} Γ t = fst $ id-out $ untyped-term Γ t empty-spans
  elab-untyped {TYPE} Γ T = fst $ id-out $ untyped-type Γ T empty-spans
  elab-untyped {KIND} Γ k = fst $ id-out $ untyped-kind Γ k empty-spans

  elab-untyped-no-params : ∀ {ed} → ctxt → ⟦ ed ⟧' → ⟦ ed ⟧
  elab-untyped-no-params Γ =
    elab-untyped (record Γ {qual = trie-map (map-snd λ _ → []) (ctxt.qual Γ)})

  {- Parsing -}
  
  ll-ind : ∀ {X : exprd → Set} → X TERM → X TYPE → X KIND → (ll : exprd) → X ll
  ll-ind t T k TERM = t
  ll-ind t T k TYPE = T
  ll-ind t T k KIND = k

  ll-ind' : ∀ {X : Σ exprd ⟦_⟧ → Set} → (s : Σ exprd ⟦_⟧) → ((t : term) → X (TERM , t)) → ((T : type) → X (TYPE , T)) → ((k : kind) → X (KIND , k)) → X s
  ll-ind' (TERM , t) tf Tf kf = tf t
  ll-ind' (TYPE , T) tf Tf kf = Tf T
  ll-ind' (KIND , k) tf Tf kf = kf k

  ll-disambiguate : ctxt → ex-tm → maybe ex-tp
  ll-disambiguate Γ (ExVar pi x) = ctxt-lookup-type-var Γ x >>= λ _ → just (ExTpVar pi x)
  ll-disambiguate Γ (ExApp t NotErased t') = ll-disambiguate Γ t >>= λ T →
    just (ExTpAppt T t')
  ll-disambiguate Γ (ExAppTp t T') = ll-disambiguate Γ t >>= λ T → just (ExTpApp T T')
  ll-disambiguate Γ (ExLam pi ff pi' x (just atk) t) =
    ll-disambiguate (ctxt-tk-decl pi' x (case atk of λ {(ExTkt _) → Tkt (TpHole pi'); (ExTkk _) → Tkk KdStar}) Γ) t >>= λ T →
    just (ExTpLam pi pi' x atk T)
  ll-disambiguate Γ (ExParens pi t pi') = ll-disambiguate Γ t
  ll-disambiguate Γ (ExLet pi _ d t) =
    ll-disambiguate (Γ' d) t >>= λ T → just (ExTpLet pi d T)
    where
    Γ' : ex-def → ctxt
    Γ' (ExDefTerm pi' x T? t) = ctxt-term-def pi' localScope opacity-open x (just (Hole pi')) (TpHole pi') Γ
    Γ' (ExDefType pi' x k T) = ctxt-type-def pi' localScope opacity-open x (just (TpHole pi')) KdStar Γ
  ll-disambiguate Γ t = nothing
  
  parse-string : (ll : exprd) → string → maybe ⟦ ll ⟧'
  parse-string ll s = case ll-ind {λ ll → string → Either string ⟦ ll ⟧'}
    parseTerm parseType parseKind ll s of λ {(Left e) → nothing; (Right e) → just e}
  
  ttk = "term, type, or kind"
  
  parse-err-msg : (failed-to-parse : string) → (as-a : string) → string
  parse-err-msg failed-to-parse "" =
    "Failed to parse \\\\\"" ^ failed-to-parse ^ "\\\\\""
  parse-err-msg failed-to-parse as-a =
    "Failed to parse \\\\\"" ^ failed-to-parse ^ "\\\\\" as a " ^ as-a
  
  infixr 7 _>>nothing_ _-_!_>>parse_ _!_>>error_
  _>>nothing_ : ∀{ℓ}{A : Set ℓ} → maybe A → maybe A → maybe A
  (nothing >>nothing m₂) = m₂
  (m₁ >>nothing m₂) = m₁
  
  _-_!_>>parse_ : ∀{A B : Set} → (string → maybe A) → string →
                  (error-msg : string) → (A → string ⊎ B) → string ⊎ B
  (f - s ! e >>parse f') = maybe-else (inj₁ (parse-err-msg s e)) f' (f s)
  
  _!_>>error_ : ∀{E A B : Set} → maybe A → E → (A → E ⊎ B) → E ⊎ B
  (just a ! e >>error f) = f a
  (nothing ! e >>error f) = inj₁ e
  
  parse-try : ∀ {X : Set} → ctxt → string → maybe
                (((ll : exprd) → ⟦ ll ⟧' → X) → X)
  parse-try Γ s =
    maybe-map (λ t f → maybe-else (f TERM t) (f TYPE) (ll-disambiguate Γ t))
      (parse-string TERM s) >>nothing
    maybe-map (λ T f → f TYPE T) (parse-string TYPE s) >>nothing
    maybe-map (λ k f → f KIND k) (parse-string KIND s)
  
  string-to-𝔹 : string → maybe 𝔹
  string-to-𝔹 "tt" = just tt
  string-to-𝔹 "ff" = just ff
  string-to-𝔹 _ = nothing
  
  parse-ll : string → maybe exprd
  parse-ll "term" = just TERM
  parse-ll "type" = just TYPE
  parse-ll "kind" = just KIND
  parse-ll _ = nothing
  
  
  {- Local Context -}
  
  record lci : Set where
    constructor mk-lci
    field ll : string; x : var; t : string; T : string; fn : string; pi : posinfo

  data 𝕃ₛ {ℓ} (A : Set ℓ) : Set ℓ where
    [_]ₛ : A → 𝕃ₛ A
    _::ₛ_ : A → 𝕃ₛ A → 𝕃ₛ A

  headₛ : ∀ {ℓ} {A : Set ℓ} → 𝕃ₛ A → A
  headₛ [ a ]ₛ = a
  headₛ (a ::ₛ as) = a

  𝕃ₛ-to-𝕃 : ∀ {ℓ} {A : Set ℓ} → 𝕃ₛ A → 𝕃 A
  𝕃ₛ-to-𝕃 [ a ]ₛ = [ a ]
  𝕃ₛ-to-𝕃 (a ::ₛ as) = a :: 𝕃ₛ-to-𝕃 as
  
  merge-lcis-ctxt-tvs : ctxt → 𝕃 string → ctxt × 𝕃 tagged-val
  merge-lcis-ctxt-tvs c =
    foldl merge-lcis-ctxt' (c , [])
      ∘ (sort-lcis ∘ strings-to-lcis)
    where
    strings-to-lcis : 𝕃 string → 𝕃 lci
    strings-to-lcis ss = strings-to-lcis-h ss [] where
      strings-to-lcis-h : 𝕃 string → 𝕃 lci → 𝕃 lci
      strings-to-lcis-h (ll :: x :: t :: T :: fn :: pi :: tl) items =
        strings-to-lcis-h tl (mk-lci ll x t T fn pi :: items)
      strings-to-lcis-h _ items = items

    -- TODO: Local context information does not pass Δ information!
    -- When users are using BR-explorer to rewrite with the rec function,
    -- if they call it upon "μ' [SUBTERM] {...}", it won't work unless they say
    -- "μ'<rec/mu> [SUBTERM] {...}".
    decl-lci : posinfo → var → ctxt → ctxt
    decl-lci pi x Γ =
      record Γ { qual = trie-insert (ctxt.qual Γ) x (pi % x , []) }

    exprd-type-of : exprd → exprd
    exprd-type-of TERM = TYPE
    exprd-type-of _ = KIND    

    merge-lci-ctxt : lci → ctxt × 𝕃 tagged-val → ctxt × 𝕃 tagged-val
    merge-lci-ctxt (mk-lci ll v t T fn pi) (Γ , tvs) =
      maybe-else (Γ , tvs) (map-snd (λ tv → tvs ++ [ tv ]))
        (parse-ll ll >>= λ ll →
         parse-string (exprd-type-of ll) T >>=
         h ll (parse-string ll t))
      where
      h : (ll : exprd) → maybe ⟦ ll ⟧' → ⟦ exprd-type-of ll ⟧' → maybe (ctxt × tagged-val)
      h TERM (just t) T =
        let t = elab-untyped Γ t
            T = elab-typed Γ T in
        return2 (ctxt-term-def pi localScope opacity-open v (just t) T Γ)
                (binder-data Γ pi v (Tkt T) ff (just t) "0" "0")
      h TYPE (just T) k =
        let T = elab-untyped Γ T
            k = elab-typed Γ k in
        return2 (ctxt-type-def pi localScope opacity-open v (just T) k Γ)
                (binder-data Γ pi v (Tkk k) ff (just T) "0" "0")
      h TERM nothing T =
        let T = elab-typed Γ T in
        return2 (ctxt-term-decl pi v T Γ)
                (binder-data Γ pi v (Tkt T) ff nothing "0" "0")
      h TYPE nothing k =
        let k = elab-typed Γ k in
        return2 (ctxt-type-decl pi v k Γ)
                (binder-data Γ pi v (Tkk k) ff nothing "0" "0")
      h _ _ _ = nothing

    merge-lcis-ctxt' : 𝕃ₛ lci → ctxt × 𝕃 tagged-val → ctxt × 𝕃 tagged-val
    merge-lcis-ctxt' ls (Γ , tvs) =
      let ls' = 𝕃ₛ-to-𝕃 ls in
      foldr merge-lci-ctxt (foldr (λ l → decl-lci (lci.pi l) (lci.x l)) Γ ls' , tvs) ls'
    
    sort-eq : ∀ {ℓ} {A : Set ℓ} → (A → A → compare-t) → 𝕃 A → 𝕃 (𝕃ₛ A)
    sort-eq {_} {A} c = foldr insert [] where
      insert : A → 𝕃 (𝕃ₛ A) → 𝕃 (𝕃ₛ A)
      insert n [] = [ [ n ]ₛ ]
      insert n (a :: as) with c (headₛ a) n
      ...| compare-eq = n ::ₛ a :: as
      ...| compare-gt = [ n ]ₛ :: a :: as
      ...| compare-lt = a :: insert n as
    
    sort-lcis : 𝕃 lci → 𝕃 (𝕃ₛ lci)
    sort-lcis = sort-eq λ l₁ l₂ →
      compare (posinfo-to-ℕ $ lci.pi l₁) (posinfo-to-ℕ $ lci.pi l₂)
    {-
    sort-lcis = list-merge-sort.merge-sort lci λ l l' →
                posinfo-to-ℕ (lci.pi l) > posinfo-to-ℕ (lci.pi l')
      where import list-merge-sort
    -}

  merge-lcis-ctxt : ctxt → 𝕃 string → ctxt
  merge-lcis-ctxt Γ ls = fst $ merge-lcis-ctxt-tvs Γ ls

  
  get-local-ctxt-tvs : ctxt → (pos : ℕ) → (local-ctxt : 𝕃 string) → ctxt × 𝕃 tagged-val
  get-local-ctxt-tvs Γ pi =
    merge-lcis-ctxt-tvs (foldr (flip ctxt-clear-symbol ∘ fst) Γ
      (flip filter (trie-mappings (ctxt.i Γ)) λ {(x , ci , fn' , pi') →
        ctxt.fn Γ =string fn' && posinfo-to-ℕ pi' > pi}))
  
  get-local-ctxt : ctxt → (pos : ℕ) → (local-ctxt : 𝕃 string) → ctxt
  get-local-ctxt Γ pi ls = fst (get-local-ctxt-tvs Γ pi ls)
  
  
  {- Helpers -}
  
  step-reduce : ∀ {ed : exprd} → ctxt → ⟦ ed ⟧ → ⟦ ed ⟧
  step-reduce Γ t =
    let t' = erase t in maybe-else t' id (step-reduceh Γ t') where
    step-reduceh : ∀ {ed : exprd} → ctxt → ⟦ ed ⟧ → maybe ⟦ ed ⟧
    step-reduceh{TERM} Γ (Var x) = ctxt-lookup-term-var-def Γ x
    step-reduceh{TYPE} Γ (TpVar x) = ctxt-lookup-type-var-def Γ x
    step-reduceh{TERM} Γ (App (Lam ff x nothing t) t') = just (subst Γ t' x t)
    step-reduceh{TYPE} Γ (TpApp (TpLam x (Tkk _) T) (Ttp T')) = just (subst Γ T' x T)
    step-reduceh{TYPE} Γ (TpApp (TpLam x (Tkt _) T) (Ttm t)) = just (subst Γ t x T)
    step-reduceh{TERM} Γ (App t t') = step-reduceh Γ t >>= λ t → just (App t t')
    step-reduceh{TYPE} Γ (TpApp T tT) = step-reduceh Γ T >>= λ T → just (TpApp T tT)
    step-reduceh{TERM} Γ (Lam ff x nothing t) = step-reduceh (ctxt-var-decl x Γ) t >>= λ t → just (Lam ff x nothing t)
    step-reduceh{TYPE} Γ (TpLam x atk T) = step-reduceh (ctxt-var-decl x Γ) T >>= λ T → just (TpLam x atk T)
    step-reduceh{TERM} Γ (LetTm ff x T t' t) = just (subst Γ t' x t)
    step-reduceh{TERM} Γ t @ (Mu μ s Tₘ f~ ms) with
      decompose-var-headed s >>=c λ sₕ sₐs → env-lookup Γ sₕ
    ...| just (ctr-def _ _ _ _ _ , _) = just (hnf Γ unfold-head-no-defs t)
    ...| _ = step-reduceh Γ s >>= λ s → just (Mu μ s Tₘ f~ ms)
    step-reduceh Γ t = nothing

  parse-norm : erased? → string → maybe (∀ {ed : exprd} → ctxt → ⟦ ed ⟧ → ⟦ ed ⟧)
  parse-norm me "all" = just λ Γ → hnf Γ (record unfold-all {unfold-erase = me})
  parse-norm me "head" = just λ Γ → hnf Γ (record unfold-all {unfold-erase = me})
  parse-norm me "once" = just λ Γ → step-reduce Γ ∘ erase
  parse-norm _ _ = nothing

  parse-norm-err = "normalization method (all, head, once)"


  {- Command Executors -}
  
  normalize-cmd : ctxt → (str ll pi norm : string) → 𝕃 string → string ⊎ tagged-val
  normalize-cmd Γ str ll pi norm ls =
    parse-ll - ll ! "language-level" >>parse λ ll' →
    string-to-ℕ - pi ! "natural number" >>parse λ sp →
    parse-norm tt - norm ! parse-norm-err >>parse λ norm →
    parse-string ll' - str ! ll >>parse λ t →
      let Γ' = get-local-ctxt Γ sp ls in
    inj₂ (to-string-tag "" Γ' (norm Γ' (elab-untyped Γ' t)))
  
  normalize-prompt : ctxt → (str norm : string) → 𝕃 string → string ⊎ tagged-val
  normalize-prompt Γ str norm ls =
    parse-norm tt - norm ! parse-norm-err >>parse λ norm →
    let Γ' = merge-lcis-ctxt Γ ls in
    parse-try Γ' - str ! ttk >>parse λ f → f λ ll t →
    inj₂ (to-string-tag "" Γ' (norm Γ' (elab-untyped Γ' t)))
  
  erase-cmd : ctxt → (str ll pi : string) → 𝕃 string → string ⊎ tagged-val
  erase-cmd Γ str ll pi ls =
    parse-ll - ll ! "language-level" >>parse λ ll' →
    string-to-ℕ - pi ! "natural number" >>parse λ sp →
    parse-string ll' - str ! ll >>parse λ t →
    let Γ' = get-local-ctxt Γ sp ls in
    inj₂ (to-string-tag "" Γ' (erase (elab-untyped Γ' t)))
  
  erase-prompt : ctxt → (str : string) → 𝕃 string → string ⊎ tagged-val
  erase-prompt Γ str ls =
    let Γ' = merge-lcis-ctxt Γ ls in
    parse-try Γ' - str ! ttk >>parse λ f → f λ ll t →
    inj₂ (to-string-tag "" Γ' (erase (elab-untyped Γ' t)))

--  private
--    cmds-to-escaped-string : cmds → strM
--    cmds-to-escaped-string (c :: cs) = cmd-to-string c $ strAdd "\\n\\n" >>str cmds-to-escaped-string cs
--    cmds-to-escaped-string [] = strEmpty

--  data-cmd : ctxt → (encoding name ps is cs : string) → string ⊎ tagged-val
--  data-cmd Γ encodingₛ x psₛ isₛ csₛ =
--    string-to-𝔹 - encodingₛ ! "boolean" >>parse λ encoding →
--    parse-string KIND - psₛ ! "kind" >>parse λ psₖ →
--    parse-string KIND - isₛ ! "kind" >>parse λ isₖ →
--    parse-string KIND - csₛ ! "kind" >>parse λ csₖ →
--    let ps = map (λ {(Index x atk) → Decl posinfo-gen posinfo-gen Erased x atk posinfo-gen}) $ kind-to-indices Γ psₖ
--        cs = map (λ {(Index x (Tkt T)) → Ctr posinfo-gen x T; (Index x (Tkk k)) → Ctr posinfo-gen x $ mtpvar "ErrorExpectedTypeNotKind"}) $ kind-to-indices empty-ctxt csₖ
--        is = kind-to-indices (add-ctrs-to-ctxt cs $ add-params-to-ctxt ps Γ) isₖ
--        picked-encoding = if encoding then mendler-encoding else mendler-simple-encoding
--        defs = datatype-encoding.mk-defs picked-encoding Γ $ Data x ps is cs in
--    inj₂ $ strRunTag "" Γ $ cmds-to-escaped-string $ fst defs

--  pretty-cmd : filepath → filepath → IO string
--  pretty-cmd src-fn dest-fn =
--    readFiniteFile src-fn >>= λ src →
--    case parseStart src of λ where
--      (Left (Left p)) → return ("Lexical error at position " ^ p)
--      (Left (Right p)) → return ("Parse error at position " ^ p)
--      (Right file) → writeFile dest-fn "" >> writeRopeToFile dest-fn (to-string.strRun empty-ctxt (to-string.file-to-string file)) >> return "Finished"
--    where import to-string (record options {pretty-print = tt}) as to-string
  
  
  {- Commands -}
  
  tv-to-json : string ⊎ tagged-val → json
  tv-to-json (inj₁ s) = json-object [ "error" , json-string s ] -- [[ "{\"error\":\"" ]] ⊹⊹ [[ s ]] ⊹⊹ [[ "\"}" ]]
  tv-to-json (inj₂ (_ , v , ts)) = tagged-vals-to-json [ "value" , v , ts ]
  
  interactive-cmd-h : ctxt → 𝕃 string → string ⊎ tagged-val
  interactive-cmd-h Γ ("normalize" :: input :: ll :: sp :: norm :: lc) =
    normalize-cmd Γ input ll sp norm lc
  interactive-cmd-h Γ ("erase" :: input :: ll :: sp :: lc) =
    erase-cmd Γ input ll sp lc
  interactive-cmd-h Γ ("normalizePrompt" :: input :: norm :: lc) =
    normalize-prompt Γ input norm lc
  interactive-cmd-h Γ ("erasePrompt" :: input :: lc) =
    erase-prompt Γ input lc
--  interactive-cmd-h Γ ("data" :: encoding :: x :: ps :: is :: cs :: []) =
--    data-cmd Γ encoding x ps is cs
  interactive-cmd-h Γ cs =
    inj₁ ("Unknown interactive cmd: " ^ 𝕃-to-string (λ s → s) ", " cs)

  record br-history : Set where
    inductive
    constructor mk-br-history
    field
      Γ : ctxt
      t : term
      Tₗₗ : exprd
      T : ⟦ Tₗₗ ⟧
      Tᵤ : string
      f : term → 𝕃 (ctr × term) → term
      Γₗ : 𝕃 tagged-val
      undo : 𝕃 br-history
      redo : 𝕃 br-history

  data br-history2 : Set where
    br-node : br-history → 𝕃 (ctr × br-history2) → br-history2
  
  br-get-h : br-history2 → br-history
  br-get-h (br-node h hs) = h

  br-lookup : 𝕃 ℕ → br-history2 → maybe br-history
  br-lookup xs h = maybe-map br-get-h $
    foldl (λ x h? → h? >>= λ {(br-node h hs) → maybe-map snd $ head2 (nthTail x hs)}) (just h) xs

  {-# TERMINATING #-}
  br-cmd2 : ctxt → string → string → string → 𝕃 string → IO ⊤
  br-cmd2 Γ Tₛ tₛ sp ls =
    (string-to-ℕ - sp ! "natural number" >>parse inj₂) >>parseIO λ sp →
    elim-pair (get-local-ctxt-tvs Γ sp ls) λ Γ Γₗ →
    (parse-try Γ - Tₛ ! ttk >>parse inj₂) >>parseIO λ Tf → Tf λ Tₗₗ T →
    (parse-string TERM - tₛ ! "term" >>parse inj₂) >>parseIO λ t →
    let T = elab-untyped Γ T
        Tₑ = erase T
        t = elab-typed Γ t in -- TODO: Probably should switch back to ex-tm so if this doesn't currently check it won't elaborate to a hole!
    putJson (tv-to-json $ inj₂ $ ts-tag Γ Tₑ) >>
    await (br-node (mk-br-history Γ t Tₗₗ T (rope-to-string $ ts2.to-string Γ Tₑ) const Γₗ [] []) [])
    where

    import to-string (record options {erase-types = ff}) as ts2
    import to-string (record options {erase-types = ff; pretty-print = tt}) as pretty2s

    ts-tag : ∀ {ed} → ctxt → ⟦ ed ⟧ → tagged-val
    ts-tag = ts2.to-string-tag ""

    infixr 6 _>>parseIO_
    _>>parseIO_ : ∀ {A : Set} → string ⊎ A → (A → IO ⊤) → IO ⊤
    inj₁ e >>parseIO f = putJson $ tv-to-json $ inj₁ e
    inj₂ a >>parseIO f = f a

    replace-substring : string → string → ℕ → ℕ → string × string
    replace-substring sₒ sᵣ fm to with string-to-𝕃char sₒ | string-to-𝕃char sᵣ
    ...| csₒ | csᵣ =
      𝕃char-to-string (take fm csₒ ++ csᵣ ++ drop to csₒ) ,
      𝕃char-to-string (take (to ∸ fm) $ drop fm csₒ)

    replace : string → string → ℕ → ℕ → string
    replace sₒ sᵣ fm to = fst $ replace-substring sₒ sᵣ fm to
    
    substring : string → ℕ → ℕ → string
    substring s fm to = snd $ replace-substring s "" fm to
    
    escape-rope : rope → rope
    escape-rope [[ s ]] = [[ escape-string s ]]
    escape-rope (r₁ ⊹⊹ r₂) = escape-rope r₁ ⊹⊹ escape-rope r₂

    parse-path : string → maybe (𝕃 ℕ)
    parse-path "" = just []
    parse-path s with string-split s ' ' | foldr (λ n ns →  ns >>= λ ns → string-to-ℕ n >>= λ n → just (n :: ns)) (just [])
    ...| "" :: ss | f = f ss
    ...| path | f = f path

    
    write-history : 𝕃 ℕ → br-history → br-history2 → br-history2
    write-history [] h (br-node _ hs) = br-node h hs
    write-history (n :: ns) h (br-node hₒ hs) = br-node hₒ $ writeh n hs where
      writeh : ℕ → 𝕃 (ctr × br-history2) → 𝕃 (ctr × br-history2)
      writeh _ [] = []
      writeh zero ((c , h') :: hs) = (c , write-history ns h h') :: hs
      writeh (suc n) (h' :: hs) = h' :: writeh n hs

    write-children : 𝕃 ℕ → 𝕃 (ctr × br-history) → br-history2 → br-history2
    write-children [] hs (br-node h _) = br-node h (map (uncurry λ c h → c , br-node h []) hs)
    write-children (n :: ns) hs (br-node h hsₒ) = br-node h $ writeh n hsₒ where
      writeh : ℕ → 𝕃 (ctr × br-history2) → 𝕃 (ctr × br-history2)
      writeh _ [] = []
      writeh zero ((c , h') :: hs') = (c , write-children ns hs h') :: hs'
      writeh (suc n) (h' :: hs) = h' :: writeh n hs

    outline : br-history2 → term
--    outline (br-node (mk-br-history Γ t TYPE T Tₛ f Γₗ undo redo) []) =
--      elim-pair (id-out $ check-term Γ t (just T) empty-spans) λ t~ ss → f t~ []
--    outline (br-node (mk-br-history Γ t Tₗₗ T Tₛ f Γₗ undo redo) []) = f (elab-untyped-no-params Γ t) []
--    outline (br-node (mk-br-history Γ t Tₗₗ T Tₛ f Γₗ undo redo) hs) =
--      f (elab-typed Γ t) (map (uncurry λ c h → c , outline h) hs)
    outline (br-node (mk-br-history Γ t Tₗₗ T Tₛ f Γₗ undo redo) hs) =
      f t (map-snd outline <$> hs)

    make-case : ctxt → params → term → case-args × term
    make-case = h [] where
      h : params → ctxt → params → term → case-args × term
      h acc Γ (Param me x atk :: ps) (Lam me' x' oc' t') =
        h (Param me x' atk :: acc) (ctxt-var-decl x' Γ) (substh-params Γ (renamectxt-single x x') empty-trie ps) t'
      h acc Γ ps (Hole pi) = params-to-case-args (reverse acc ++ ps) , Hole pi
      h acc Γ ps t = params-to-case-args (reverse acc ++ ps) , params-to-apps ps t

    await : br-history2 → IO ⊤
    awaith : br-history2 → 𝕃 string → IO ⊤
    await his =
      getLine >>= λ input →
      let input = undo-escape-string input
          as = string-split input delimiter in
      awaith his as
    
    awaith his as =
      let put = putJson ∘ tv-to-json
          err = (_>> await his) ∘' put ∘' inj₁ in
      case as of λ where -- TODO: for these commands, do not add TYPES/KINDS of local decls to context, as they are probably just bound by foralls/pis/lambdas, not _really_ in scope!
        ("br" :: path :: as) →
          maybe-else' (parse-path path) (err ("Could not parse " ^ path ^ " as a list of space-delimited natural numbers")) λ path →
          let await-with = await ∘ flip (write-history path) his in
          maybe-else' (br-lookup path his) (err "Beta-reduction pointer does not exist") λ where
            this @ (mk-br-history Γ t Tₗₗ T Tᵤ f Γₗ undo redo) → case as of λ where
             
              ("undo" :: []) → case undo of λ where
                [] → err "No undo history"
                (u :: us) →
                  put (inj₂ $ "" , [[ "Undo" ]] , []) >>
                  await-with (record u {undo = us; redo = this :: redo})
                  --u (await Γ t Tₗₗ T Tᵤ f undo redo :: redo)
             
              ("redo" :: []) → case redo of λ where
                [] → err "No redo history"
                (r :: rs) →
                  put (inj₂ $ "" , [[ "Redo" ]] , []) >>
                  await-with (record r {undo = this :: undo; redo = rs})
                  --r
             
              ("get" :: []) →
                put (inj₂ $ "" , [[ Tᵤ ]] , []) >>
                await his
             
              ("parse" :: []) →
                (_>> await his) $
                maybe-else' (parse-string Tₗₗ Tᵤ)
                  (putJson $ spans-to-json $ global-error "Parse error" nothing)
                  λ T → putJson $ spans-to-json $ snd $ id-out $ ll-ind {λ ll → ctxt → ⟦ ll ⟧' → spanM ⟦ ll ⟧}
                          untyped-term untyped-type untyped-kind Tₗₗ (record Γ { fn = "missing" }) T empty-spans

              ("context" :: []) →
                putJson (json-object [ "value" , json-array [ tagged-vals-to-json Γₗ ] ]) >> await his
             
              ("check" :: t?) →
                let await-set = maybe-else (await his) λ t → await-with $ record this
                                  {t = t; undo = this :: undo; redo = []} in
                (λ e → either-else' e
                  (uncurry λ t? e → put (inj₁ e) >> await-set t?)
                  (uncurry λ t? m → put (inj₂ $ "value" , [[ m ]] , []) >> await-set t?)) $
                ll-ind' {λ T → (maybe term × string) ⊎ (maybe term × string)} (Tₗₗ , T)
                  (λ _ → inj₁ $ nothing , "Expression must be a type, not a term!")
                  (λ T →
                    (case t? of λ where
                      [] → inj₂ nothing
                      (t :: []) → maybe-else' (parse-string TERM t)
                        (inj₁ $ nothing , parse-err-msg t "term")
                        (inj₂ ∘ just)
                      _ → inj₁ $ nothing ,
                        "To many arguments given to beta-reduction command 'check'")
                  >>= λ t? →
                    elim-pair (maybe-else' t? (elim-pair (id-out (check-term (qualified-ctxt Γ) (resugar t) (just T) empty-spans)) λ t~ ss → nothing , spans-have-error ss)
                                 λ t → elim-pair (id-out (check-term Γ t (just T) empty-spans))
                                         λ t~ ss → just t~ , spans-have-error ss) λ t~? e? →
                    let fail = inj₁ (just (maybe-else' t~? t id) , "Type error")
                        try-β = elim-pair (id-out (check-term Γ (ExBeta pi-gen nothing nothing) (just T) empty-spans)) λ β~ ss → if spans-have-error ss then inj₁ (nothing , "Type error") else inj₂ (just β~ , "Equal by beta") in
                    if e?
                      then if isJust t? then fail else try-β
                      else inj₂ (t~? , "Type inhabited"))
                  (λ _ → inj₁ $ nothing , "Expression must be a type, not a kind!")
             
              ("rewrite" :: fm :: to :: eq :: ρ+? :: lc) →
                let Γ' = merge-lcis-ctxt Γ lc in
                either-else'
                  (parse-string TERM - eq ! "term" >>parse λ eqₒ →
                   string-to-𝔹 - ρ+? ! "boolean" >>parse λ ρ+? →
                   string-to-ℕ - fm ! "natural number" >>parse λ fm →
                   string-to-ℕ - to ! "natural number" >>parse λ to →
                   parse-try Γ' - substring Tᵤ fm to ! ttk >>parse λ Tf → Tf λ ll Tₗ →
                   elim-pair (id-out (check-term Γ' eqₒ nothing empty-spans)) $ uncurry λ eq Tₑ ss →
                   is-eq-tp? Tₑ ! "Synthesized a non-equational type from the proof"
                     >>error uncurry λ t₁ t₂ →
                   err⊎-guard (spans-have-error ss) "Proof does not type check" >>
                   let Tₑ = TpEq t₁ t₂
                       x = fresh-var Γ' "x"
                       Tₗ = elab-untyped-no-params Γ' Tₗ in
                   elim-pair (map-snd snd $ rewrite-exprd Tₗ Γ' ρ+? nothing (just eq) t₁ x 0) λ Tᵣ n →
                   err⊎-guard (iszero n) "No rewrites could be performed" >>
                   parse-string Tₗₗ - replace Tᵤ
                     (rope-to-string $ [[ "(" ]] ⊹⊹ ts2.to-string Γ' Tᵣ ⊹⊹ [[ ")" ]]) fm to
                     ! ll-ind "term" "type" "kind" Tₗₗ >>parse λ Tᵤ →
                   let Tᵤ = elab-untyped-no-params (ctxt-var-decl x Γ) Tᵤ in
                   ll-ind' {λ {(ll , T) → ⟦ ll ⟧ → string ⊎ ⟦ ll ⟧ × (term → term)}}
                     (Tₗₗ , Tᵤ)
                     (λ t T → inj₂ $ rewrite-mk-phi x eq T (subst Γ t₂ x t) , id)
                     (λ Tᵤ _ → inj₂ $ post-rewrite (ctxt-var-decl x Γ) x eq t₂ Tᵤ ,
                                      Rho eq x Tᵤ)
                     (λ k _ → inj₂ $ subst Γ t₂ x k , id)
                     T) err $ uncurry λ T' fₜ →
                  put (inj₂ $ ts-tag Γ $ erase T') >>
                  await-with (record this {T = T'; Tᵤ = rope-to-string $ ts2.to-string Γ $ erase T'; f = f ∘ fₜ; undo = this :: undo; redo = []})
             
              ("normalize" :: fm :: to :: norm :: lc) →
                either-else'
                  (let Γ' = merge-lcis-ctxt Γ lc in
                   string-to-ℕ - fm ! "natural number" >>parse λ fm →
                   string-to-ℕ - to ! "natural number" >>parse λ to →
                   let tₛ = substring Tᵤ fm to in
                   parse-try Γ' - tₛ ! ttk >>parse λ t → t λ ll t →
                   parse-norm ff - norm ! parse-norm-err >>parse λ norm →
                   let s = norm Γ' $ elab-untyped-no-params Γ' t
                       rs = rope-to-string $ [[ "(" ]] ⊹⊹ ts2.to-string Γ' s ⊹⊹ [[ ")" ]]
                       Tᵤ' = replace Tᵤ rs fm to in
                   parse-string Tₗₗ - Tᵤ' ! ll-ind "term" "type" "kind" Tₗₗ >>parse λ Tᵤ' →
                   let Tᵤ' = elab-untyped-no-params Γ' Tᵤ' in
                   inj₂ Tᵤ')
                  err λ Tᵤ' →
                  put (inj₂ $ ts-tag Γ Tᵤ') >>
                  await-with (record this {T = Tᵤ' {-Checks?-}; Tᵤ = rope-to-string $ ts2.to-string Γ $ erase Tᵤ'; undo = this :: undo; redo = []})
             
              ("conv" :: ll :: fm :: to :: t' :: ls) →
                let Γ' = merge-lcis-ctxt Γ ls in
                either-else'
                  (parse-ll - ll ! "language level" >>parse λ ll →
                   string-to-ℕ - fm ! "natural number" >>parse λ fm →
                   string-to-ℕ - to ! "natural number" >>parse λ to →
                   let t = substring Tᵤ fm to in
                   parse-string ll - t  ! ll-ind "term" "type" "kind" ll >>parse λ t  →
                   parse-string ll - t' ! ll-ind "term" "type" "kind" ll >>parse λ t' →
                   let t = elab-untyped-no-params Γ' t; t' = elab-untyped-no-params Γ' t' in
                   err⊎-guard (~ ll-ind {λ ll → ctxt → ⟦ ll ⟧ → ⟦ ll ⟧ → 𝔹}
                     conv-term conv-type conv-kind ll Γ' t t') "Inconvertible" >>
                   let rs = [[ "(" ]] ⊹⊹ ts2.to-string Γ' (erase t') ⊹⊹ [[ ")" ]]
                       Tᵤ = replace Tᵤ (rope-to-string rs) fm to in
                   parse-string Tₗₗ - Tᵤ ! ll-ind "term" "type" "kind" Tₗₗ >>parse λ Tᵤ →
                   inj₂ (elab-untyped-no-params Γ Tᵤ)) err λ Tᵤ' →
                  put (inj₂ $ ts-tag Γ $ erase Tᵤ') >>
                  await-with (record this {Tᵤ = rope-to-string $ ts2.to-string Γ $ erase Tᵤ'; undo = this :: undo; redo = []})
             
              ("bind" :: xᵤ :: []) →
                let Γₚᵢ = ℕ-to-string (length Γₗ) in
                either-else'
                  (ll-ind' {λ {(ll , _) → string ⊎ ctxt × erased? × tpkd × ⟦ ll ⟧ × (term → term)}} (Tₗₗ , T)
                    (λ t' →
                      let R = string ⊎ ctxt × erased? × tpkd × term × (term → term) in
                      (case_of_ {B = (erased? → var → maybe tpkd → term → R) → R}
                        (t' , hnf Γ unfold-head t') $ uncurry λ where
                          (Lam me x oc body) _ f → f me x oc body
                          _ (Lam me x oc body) f → f me x oc body
                          _ _ _ → inj₁ "Not a term abstraction") λ me x oc body →
                      inj₂ $ ctxt-var-decl-loc Γₚᵢ xᵤ Γ ,
                             me ,
                             maybe-else' oc (Tkt $ TpHole pi-gen) id ,
                             rename-var (ctxt-var-decl-loc Γₚᵢ xᵤ Γ) x xᵤ body ,
                             Lam me xᵤ oc)
                    (λ T → Γ ⊢ T =β= λ where
                      (TpAbs me x dom cod) →
                        let Γ' = ctxt-tk-decl Γₚᵢ xᵤ dom Γ in
                        inj₂ $ Γ' ,
                               me ,
                               dom ,
                               rename-var Γ' x (Γₚᵢ % xᵤ) cod ,
                               Lam me xᵤ (just dom)
                      _ → inj₁ "Not a type abstraction")
                    (λ k → inj₁ "Expression must be a term or a type"))
                  err λ where
                    (Γ' , me , dom , cod , fₜ) →
                      let tv = binder-data Γ' Γₚᵢ xᵤ dom me nothing "0" "0" in
--                      putJson (json-object [ "value" , json-array (json-array (json-rope (fst (snd tv)) :: json-rope (to-string Γ' $ erase cod) :: []) :: []) ]) >>
                      putJson (json-object [ "value" , json-array [ json-rope (to-string Γ' $ erase cod) ] ]) >>
                      await-with (record this
                        {Γ = Γ' ;
                         T = cod;
                         Tᵤ = rope-to-string $ ts2.to-string Γ' $ erase cod;
                         f = f ∘ fₜ;
                         Γₗ = Γₗ ++ [ tv ];
                         undo = this :: undo;
                         redo = []})
             
              ("case" :: scrutinee :: rec :: motive?) → -- TODO: Motive?
                let Γₚᵢ = ℕ-to-string (length Γₗ) in
                either-else'
                  (parse-string TERM - scrutinee ! "term" >>parse λ scrutinee →
                   elim-pair (id-out (check-term Γ scrutinee nothing empty-spans)) $ uncurry λ tₛ Tₛ ss →
                   if (spans-have-error ss) then inj₁ "Error synthesizing a type from the input term"
                   else
                   let Tₛ = hnf Γ unfold-no-defs Tₛ in
                   case decompose-ctr-type Γ Tₛ of λ where
                     (TpVar Xₛ , [] , as) →
                       ll-ind' {λ T → string ⊎ (term × term × 𝕃 (ctr × type) × type × ctxt × 𝕃 tagged-val × datatype-info)} (Tₗₗ , T)
                         (λ t → inj₁ "Expression must be a type to case split")
                         (λ T → maybe-else' (data-lookup Γ Xₛ as)
                           (inj₁ "The synthesized type of the input term is not a datatype")
                           λ d → let mk-data-info X _ asₚ asᵢ ps kᵢ k cs csₚₛ _ _ = d
                                     is' = kind-to-indices (add-params-to-ctxt ps Γ) kᵢ
                                     is = drop-last 1 is'
                                     Tₘ = refine-motive Γ is' (asᵢ ++ [ Ttm tₛ ]) T
                                     sM' = ctxt-mu-decls Γ tₛ is Tₘ d Γₚᵢ "0" "0" rec
                                     σ = λ y → inst-ctrs Γ ps asₚ (map-snd (rename-var {TYPE} Γ X y) <$> cs)
                                     sM = if rec =string ""
                                             then (σ X , const spanMok , Γ , [] , empty-renamectxt , (λ Γ t T → t) , (λ Γ T k → T))
                                             else (σ (Γₚᵢ % mu-Type/ rec) , sM')
                                     mu = sigma-build-evidence Xₛ d in
                             case sM of λ where
                               (σ-cs , _ , Γ' , ts , ρ , tf , Tf) →
                                 if spans-have-error (snd $ id-out $
                                      check-type (qualified-ctxt Γ) (resugar Tₘ) (just kᵢ) empty-spans)
                                   then inj₁ "Computed an ill-typed motive"
                                   else inj₂ (
                                     tₛ ,
                                     mu ,
                                     map (λ {(Ctr x T) →
                                       let T' = hnf Γ' unfold-head-elab T in
                                       Ctr x T ,
                                       (case decompose-ctr-type Γ' T' of λ {(Tₕ , ps' , as) →
                                         params-to-alls ps' $ hnf Γ' unfold-head-no-defs (TpApp
                                           (recompose-tpapps (drop (length ps) as) Tₘ)
                                           (Ttm (recompose-apps (params-to-args ps') $
                                             recompose-apps asₚ (Var x))))})})
                                       σ-cs ,
                                     Tₘ ,
                                     Γ' ,
                                     ts ,
                                     d))
                         (λ k → inj₁ "Expression must be a type to case split")
                     (Tₕ , [] , as) → inj₁ "Synthesized a non-datatype from the input term"
                     (Tₕ , ps , as) →
                       inj₁ "Case splitting is currently restricted to datatypes")
                err $ λ where
                 (scrutinee , mu , cs , Tₘ , Γ , ts , d) →
                   let json = json-object [ "value" , json-array
                                   [ json-object (map
                                    (λ {(Ctr x _ , T) → unqual-all (ctxt.qual Γ) x ,
                                      json-rope (to-string Γ (erase T))})
                                    cs) ] ] in -- ) ] ] in
                   putJson json >>
                   let shallow = iszero (string-length rec)
                       mk-cs = map λ where
                         (Ctr x T , t) →
                           let T' = hnf Γ unfold-head-elab T in
                           case decompose-ctr-type Γ T' of λ where
                             (Tₕ , ps , as) →
                               elim-pair (make-case Γ ps t) λ cas t → Case x cas t []
                       f'' = λ t cs → (if shallow then Mu rec else Sigma (just mu)) t (just Tₘ) d (mk-cs cs)
                       f' = λ t cs → f (f'' t cs) cs
                       mk-hs = map $ map-snd λ T'' →
                                 mk-br-history Γ t TYPE T''
                                   (rope-to-string $ to-string Γ $ erase T'')
                                   (λ t cs → t) (Γₗ ++ ts) [] [] in
                   await (write-children path (mk-hs cs) $
                            write-history path (record this
                              {f = f';
                               Γ = Γ;
                               t = scrutinee;
                               Γₗ = Γₗ ++ ts;-- TODO: Should we really do this?
                               undo = this :: undo;
                               redo = []})
                              his)

              ("print" :: tab :: []) →
                either-else' (string-to-ℕ - tab ! "natural number" >>parse inj₂) err λ tab →
                putRopeLn (escape-rope (json-to-rope (tv-to-json (inj₂ $ pretty2s.strRunTag "" Γ $ pretty2s.strNest (suc {-left paren-} tab) (pretty2s.to-stringh $ outline his))))) >> await his
              
              ("quit" :: []) → put $ inj₂ $ strRunTag "" Γ $ strAdd "Quitting beta-reduction mode..."
             
              _ → err $ foldl (λ a s → s ^ char-to-string delimiter ^ a)
                      "Unknown beta-reduction command: " as
        _ → err "A beta-reduction buffer is still open"




interactive-cmd : 𝕃 string → toplevel-state → IO ⊤
interactive-cmd ("br2" :: T :: t :: sp :: lc) ts = br-cmd2 (toplevel-state.Γ ts) T t sp lc
--interactive-cmd ("pretty" :: src :: dest :: []) ts = pretty-cmd src dest >>= putStrLn
interactive-cmd ls ts = putRopeLn (json-to-rope (tv-to-json (interactive-cmd-h (toplevel-state.Γ ts) ls)))

interactive-not-br-cmd-msg = tv-to-json $ inj₁ "Beta-reduction mode has been terminated"
