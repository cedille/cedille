module Norm where
import Types
import Trie

headOr []       a' = a'
headOr (a : as) a' = a

type CtxtDef = Either (PrTerm, PrType) (PrType, PrKind)
data Ctxt = Ctxt [PrTmTp] [PrTpKd] (Trie CtxtDef) (Trie ())

emptyCtxt = Ctxt [] [] emptyTrie emptyTrie

ctxtDecl (Ctxt decls types defs scope) decl =
  Ctxt (decl : decls) types defs scope
ctxtDeclType (Ctxt decls types defs scope) decl tp =
  -- Increment all free variables to account for this itself being declared
  Ctxt (decl : decls) (mapTpKd' (deltaType 1) (deltaKind 1) tp : types) defs scope
ctxtDef (Ctxt decls types defs scope) x def =
  Ctxt decls types (trieInsert defs x def) (trieInsert scope x ())
ctxtDeclTpKd c = either
  (ctxtDeclType c tmDecl . Left)
  (ctxtDeclType c tpDecl . Right)

tmDecl = Left (PrVar 0)
tpDecl = Right (TpVar 0)
tkDecl = either (const tmDecl) (const tpDecl)

ctxtLookupDef (Ctxt decls types defs scope) x =
  trieLookup scope x >> trieLookup defs x
ctxtLookupDeclType (Ctxt decls types defs scope) i
  | i >= length types = Nothing
  | otherwise = Just $ mapTpKd' (deltaType i) (deltaKind i) (types !! i)
ctxtLookupDecl (Ctxt decls types defs scope) i
  | i >= length decls = Nothing
  | otherwise = Just (decls !! i)

ctxtLookupTermDef c v = ctxtLookupDef c v >>= either Just (const Nothing)
ctxtLookupTypeDef c v = ctxtLookupDef c v >>= either (const Nothing) Just


erasePrTermh e c (PrVar k) = PrVar (if k < length c then k + (c !! k) - head c else k - e)
erasePrTermh e c (PrRef v) = PrRef v
erasePrTermh e c (PrApp tm tm') = PrApp (erasePrTermh e c tm) (erasePrTermh e c tm')
erasePrTermh e c (PrLam tm) = PrLam (erasePrTermh e (headOr c 0 : c) tm)

eraseTermh e c (TmVar k) = PrVar (if k < length c then k + (c !! k) - head c else k - e)
eraseTermh e c (TmRef v) = PrRef v
eraseTermh e c (TmLam _ t) = PrLam (eraseTermh e (headOr c 0 : c) t)
eraseTermh e c (TmLamE _ t) = eraseTermh (succ e) (succ (headOr c 0) : c) t
eraseTermh e c (TmAppTm t t') = PrApp (eraseTermh e c t) (eraseTermh e c t')
eraseTermh e c (TmAppTmE t _) = eraseTermh e c t
eraseTermh e c (TmAppTp t _) = eraseTermh e c t
eraseTermh e c (TmIota t _ _) = eraseTermh e c t
eraseTermh e c (TmLetTm t t') = PrApp (PrLam (eraseTermh e (headOr c 0 : c) t')) (eraseTermh e c t)
eraseTermh e c (TmLetTmE _ t) = eraseTermh (succ e) (succ (headOr c 0) : c) t
eraseTermh e c (TmLetTp _ _ t) = eraseTermh (succ e) (succ (headOr c 0) : c) t
eraseTermh e c (TmProj1 t) = eraseTermh e c t
eraseTermh e c (TmProj2 t) = eraseTermh e c t
eraseTermh e c (TmBeta _ t) = erasePrTermh e c t
eraseTermh e c (TmSigma t) = eraseTermh e c t
eraseTermh e c (TmDelta _ t) = eraseTermh e c t
eraseTermh e c (TmRho _ _ t) = eraseTermh e c t
eraseTermh e c (TmPhi _ _ t) = erasePrTermh e c t
eraseTerm = eraseTermh 0 []

eraseTypeh e c (TpVar k) = TpVar (if k < length c then k + (c !! k) - head c else k - e)
eraseTypeh e c (TpRef v) = TpRef v
eraseTypeh e c (TpLam tk tp) = TpLam (eraseTpKdh e c tk) (eraseTypeh e (headOr c 0 : c) tp)
eraseTypeh e c (TpAll tk tp) = TpAll (eraseTpKdh e c tk) (eraseTypeh e (headOr c 0 : c) tp)
eraseTypeh e c (TpPi tp tp') = TpPi (eraseTypeh e c tp) (eraseTypeh e (headOr c 0 : c) tp')
eraseTypeh e c (TpEq tm tm') = TpEq (erasePrTermh e c tm) (erasePrTermh e c tm')
eraseTypeh e c (TpAppTp tp tp') = TpAppTp (eraseTypeh e c tp) (eraseTypeh e c tp')
eraseTypeh e c (TpAppTm tp tm) = TpAppTm (eraseTypeh e c tp) (eraseTermh e c tm)
eraseTypeh e c (TpIota tp tp') = TpIota (eraseTypeh e c tp) (eraseTypeh e (headOr c 0 : c) tp')
eraseType = eraseTypeh 0 []

eraseKindh e c KdStar = KdStar
eraseKindh e c (KdPi tk kd) = KdPi (eraseTpKdh e c tk) (eraseKindh e (headOr c 0 : c) kd)
eraseKind = eraseKindh 0 []

eraseTpKdh = mapTpKd eraseTypeh eraseKindh
eraseTpKd = eraseTpKdh 0 []

freeInTerm = h 0 . eraseTerm where
  h i (PrVar j) = i == j
  h i (PrRef v) = False
  h i (PrApp tm tm') = h i tm || h i tm'
  h i (PrLam tm) = h (succ i) tm

mapTpKd' f g = either (Left . f) (Right . g)
mapTpKd f g a b = mapTpKd' (f a b) (g a b)

deltaTermh r d (PrVar j)      = PrVar (if j >= r then j + d else j)
deltaTermh r d (PrRef v)      = PrRef v
deltaTermh r d (PrApp tm tm') = PrApp (deltaTermh r d tm) (deltaTermh r d tm')
deltaTermh r d (PrLam tm)     = PrLam (deltaTermh (succ r) d tm)

deltaTypeh r d (TpVar j)        = TpVar (if j >= r then j + d else j)
deltaTypeh r d (TpRef v)        = TpRef v
deltaTypeh r d (TpLam tk tp)    = TpLam    (deltaTpKdh r d tk) (deltaTypeh (succ r) d tp)
deltaTypeh r d (TpAll tk tp)    = TpAll    (deltaTpKdh r d tk) (deltaTypeh (succ r) d tp)
deltaTypeh r d (TpPi tp tp')    = TpPi     (deltaTypeh r d tp) (deltaTypeh (succ r) d tp')
deltaTypeh r d (TpIota tp tp')  = TpIota   (deltaTypeh r d tp) (deltaTypeh (succ r) d tp')
deltaTypeh r d (TpEq tm tm')    = TpEq     (deltaTermh r d tm) (deltaTermh r        d tm')
deltaTypeh r d (TpAppTp tp tp') = TpAppTp  (deltaTypeh r d tp) (deltaTypeh r        d tp')
deltaTypeh r d (TpAppTm tp tm)  = TpAppTm  (deltaTypeh r d tp) (deltaTermh r        d tm)

deltaKindh r d KdStar = KdStar
deltaKindh r d (KdPi tk kd) = KdPi (deltaTpKdh r d tk) (deltaKindh (succ r) d kd)

deltaTpKdh = mapTpKd deltaTypeh deltaKindh

substTermh i z (PrVar j) = case compare j i of
  LT -> PrVar j
  EQ -> either (deltaTerm i) (const $ PrVar j) z
  GT -> PrVar (pred j)
substTermh i z (PrRef v)      = PrRef v
substTermh i z (PrApp tm tm') = PrApp (substTermh i z tm) (substTermh i z tm')
substTermh i z (PrLam tm)     = PrLam (substTermh (succ i) z tm)


substTypeh i z (TpVar j) = case compare j i of
  LT -> TpVar j
  EQ -> either (const $ TpVar j) (deltaType i) z
  GT -> TpVar (pred j)
substTypeh i z (TpRef v)        = TpRef v
substTypeh i z (TpLam tk tp)    = TpLam   (substTpKdh i z tk) (substTypeh (succ i) z tp)
substTypeh i z (TpAll tk tp)    = TpAll   (substTpKdh i z tk) (substTypeh (succ i) z tp)
substTypeh i z (TpPi tp tp')    = TpPi    (substTypeh i z tp) (substTypeh (succ i) z tp')
substTypeh i z (TpIota tp tp')  = TpIota  (substTypeh i z tp) (substTypeh (succ i) z tp')
substTypeh i z (TpEq tm tm')    = TpEq    (substTermh i z tm) (substTermh i        z tm')
substTypeh i z (TpAppTp tp tp') = TpAppTp (substTypeh i z tp) (substTypeh i        z tp')
substTypeh i z (TpAppTm tp tm)  = TpAppTm (substTypeh i z tp) (substTermh i        z tm)

substKindh i z KdStar = KdStar
substKindh i z (KdPi tk kd) = KdPi (substTpKdh i z tk) (substKindh (succ i) z kd)

substTpKdh = mapTpKd substTypeh substKindh


hnfTermh i (Ctxt decls _ _ _) (PrVar j)
  | j >= i && j < i + length decls = either (deltaTerm j) (const $ PrVar j) (decls !! (j - i))
  | otherwise = PrVar j
hnfTermh i (Ctxt _ _ defs _) (PrRef v) =
  maybe (PrRef v) id (trieLookup defs v >>= either (Just . fst) (const Nothing))
hnfTermh i c (PrApp tm tm') =
  case hnfTermh i c tm of
    (PrLam btm) -> hnfTermh i c (substTerm (Left tm') btm)
    htm -> PrApp htm tm'
hnfTermh i c (PrLam tm) = PrLam (hnfTermh (succ i) c tm)

hnfTypeh i (Ctxt decls _ _ _) (TpVar j)
  | j >= i && j < i + length decls = either (const $ TpVar j) (deltaType j) (decls !! (j - i))
  | otherwise = TpVar j
hnfTypeh i (Ctxt _ _ defs _) (TpRef v) = 
  maybe (TpRef v) id (trieLookup defs v >>= either (const Nothing) (Just . fst))
hnfTypeh i c (TpLam tk tp)    = TpLam tk (hnfTypeh (succ i) c tp)
hnfTypeh i c (TpAll tk tp)    = TpAll tk (hnfTypeh (succ i) c tp)
hnfTypeh i c (TpPi tp tp')    = TpPi  tp (hnfTypeh (succ i) c tp')
hnfTypeh i c (TpIota tp tp')  = TpIota tp tp'
hnfTypeh i c (TpEq tm tm')    = TpEq tm tm'
hnfTypeh i c (TpAppTp tp tp') =
  case hnfTypeh i c tp of
    (TpLam (Right _) btp) -> hnfTypeh i c (substType (Right tp') btp)
    htp -> TpAppTp htp tp'
hnfTypeh i c (TpAppTm tp tm) =
  case hnfTypeh i c tp of
    (TpLam (Left _) btp) -> hnfTypeh i c (substType (Left tm) btp)
    htp -> TpAppTm htp tm

hnfKindh i c k = k

hnfTpKdh = mapTpKd hnfTypeh hnfKindh


convTermh c (PrVar i1) (PrVar i2) = i1 == i2
convTermh c (PrRef v1) (PrRef v2) = v1 == v2
convTermh c (PrApp tm1 tm1') (PrApp tm2 tm2') =
  convTermh c tm1 tm2 && convTerm c tm1' tm2'
convTermh c (PrLam tm1) (PrLam tm2) =
  convTermh (ctxtDecl c tmDecl) tm1 tm2
convTermh c (PrLam tm1) tm2 =
  convTerm (ctxtDecl c tmDecl) tm1 (PrApp (deltaTerm 1 tm2) (PrVar 0))
convTermh c tm1 (PrLam tm2) =
  convTerm (ctxtDecl c tmDecl) (PrApp (deltaTerm 1 tm1) (PrVar 0)) tm2
convTermh _ _ _ = False

convTypeh c (TpVar i1) (TpVar i2) = i1 == i2
convTypeh c (TpRef v1) (TpRef v2) = v1 == v2
convTypeh c (TpAll tk1 tp1) (TpAll tk2 tp2) =
  convTpKd c tk1 tk2 && convTypeh (ctxtDecl c (tkDecl tk1)) tp1 tp2
convTypeh c (TpLam tk1 tp1) (TpLam tk2 tp2) =
  convTpKd c tk1 tk2 && convTypeh (ctxtDecl c (tkDecl tk1)) tp1 tp2
convTypeh c (TpPi tp1 tp1') (TpPi tp2 tp2') =
  convType c tp1 tp2 && convTypeh (ctxtDecl c tmDecl) tp1' tp2'
convTypeh c (TpIota tp1 tp1') (TpIota tp2 tp2') =
  convType c tp1 tp2 && convType (ctxtDecl c tmDecl) tp1' tp2'
convTypeh c (TpEq tm1 tm1') (TpEq tm2 tm2') =
  convTerm c tm1 tm2 && convTerm c tm1' tm2'
convTypeh c (TpAppTp tp1 tp1') (TpAppTp tp2 tp2') =
  convTypeh c tp1 tp2 && convType c tp1' tp2'
convTypeh c (TpAppTm tp1 tm1) (TpAppTm tp2 tm2) =
  convTypeh c tp1 tp2 && convTerm c tm1 tm2
convTypeh _ _ _ = False

convKindh c KdStar KdStar = True
convKindh c (KdPi tk1 kd1) (KdPi tk2 kd2) =
  convTpKd c tk1 tk2 && convKind (ctxtDecl c (tkDecl tk1)) kd1 kd2
convKindh c _ _ = False

convTpKdh c (Left tp) (Left tp') = convTypeh c tp tp'
convTpKdh c (Right kd) (Right kd') = convKindh c kd kd'
convTpKdh c _ _ = False

deltaTerm = deltaTermh 0
deltaType = deltaTypeh 0
deltaKind = deltaKindh 0
deltaTpKd = deltaTpKdh 0

hnfTerm = hnfTermh 0
hnfType = hnfTypeh 0
hnfKind = hnfKindh 0
hnfTpKd = hnfTpKdh 0

hnfeTerm c = hnfTerm c . eraseTerm
hnfeType c = hnfType c . eraseType
hnfeKind c = hnfKind c . eraseKind
hnfeTpKd c = hnfTpKd c . eraseTpKd

substTerm = substTermh 0
substType = substTypeh 0
substKind = substKindh 0
substTpKd = substTpKdh 0

convTerm c tm tm' = convTermh c tm tm' || convTermh c (hnfTerm c tm) (hnfTerm c tm')
convType c tp tp' = convTypeh c tp tp' || convTypeh c (hnfType c tp) (hnfType c tp')
convKind c kd kd' = convKindh c kd kd' || convKindh c (hnfKind c kd) (hnfKind c kd')
convTpKd c tk tk' = convTpKdh c tk tk' || convTpKdh c (hnfTpKd c tk) (hnfTpKd c tk')
