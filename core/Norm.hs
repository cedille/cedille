module Norm where
import Types
import Trie

headOr []       a' = a'
headOr (a : as) a' = a

tkElim tp kd (TpKdTp tktp) = tp tktp
tkElim tp kd (TpKdKd tkkd) = kd tkkd
tkIs = tkElim (const True) (const False)

ifM b = if b then Just () else Nothing

data CtxtDef =
    TermDef PureTerm PureType
  | TypeDef PureType PureKind
data CtxtDecl =
    TermDecl PureTerm
  | TypeDecl PureType
  | KindDecl PureKind
data Ctxt = Ctxt [CtxtDecl] [CtxtDecl] (Trie CtxtDef) (Trie ())

emptyCtxt = Ctxt [] [] emptyTrie emptyTrie

ctxtDefElim  ftm ftp (TermDef tm tp) = ftm tm tp
ctxtDefElim  ftm ftp (TypeDef tp kd) = ftp tp kd
ctxtDeclElim ftm ftp fkd (TermDecl tm) = ftm tm
ctxtDeclElim ftm ftp fkd (TypeDecl tp) = ftp tp
ctxtDeclElim ftm ftp fkd (KindDecl kd) = fkd kd

ctxtDecl (Ctxt decls types defs scope) decl =
  Ctxt (decl : decls) types defs scope
ctxtDeclType (Ctxt decls types defs scope) decl tp =
  Ctxt (decl : decls) (deltaDecl 1 tp : types) defs scope
ctxtDef (Ctxt decls types defs scope) x def =
  Ctxt decls types (trieInsert defs x def) (trieInsert scope x ())
ctxtDeclTpKd c = tkElim
  (ctxtDeclType c termDecl . TypeDecl)
  (ctxtDeclType c typeDecl . KindDecl)

termDecl = TermDecl (PureVar 0)
typeDecl = TypeDecl (TpVar 0)

ctxtLookupDef (Ctxt decls types defs scope) x =
  trieLookup scope x >> trieLookup defs x
ctxtLookupDeclType (Ctxt decls types defs scope) i
  | i >= length types = Nothing
  | otherwise = Just $ deltaDecl i (types !! i)
ctxtLookupDecl (Ctxt decls types defs scope) i
  | i >= length decls = Nothing
  | otherwise = Just (decls !! i)
  
ctxtLookupTermDecl c i = case ctxtLookupDecl c i of
  Just (TermDecl tm) -> Just $ deltaTerm i tm
  _ -> Nothing

ctxtLookupTypeDecl c i = case ctxtLookupDecl c i of
  Just (TypeDecl tp) -> Just $ deltaType i tp
  _ -> Nothing

ctxtLookupTermDef c v = case ctxtLookupDef c v of
  Just (TermDef tm tp) -> Just (tm, tp)
  _ -> Nothing
  
ctxtLookupTypeDef c v = case ctxtLookupDef c v of
  Just (TypeDef tp kd) -> Just (tp, kd)
  _ -> Nothing

erasePureTermh e c (PureVar k) = PureVar (if k < length c then k + (c !! k) - head c else k - e)
erasePureTermh e c (PureRef v) = PureRef v
erasePureTermh e c (PureApp tm tm') = PureApp (erasePureTermh e c tm) (erasePureTermh e c tm')
erasePureTermh e c (PureLam tm) = PureLam (erasePureTermh e (headOr c 0 : c) tm)

eraseTermh e c (TmVar k) = PureVar (if k < length c then k + (c !! k) - head c else k - e)
eraseTermh e c (TmRef v) = PureRef v
eraseTermh e c (TmLam _ t) = PureLam (eraseTermh e (headOr c 0 : c) t)
eraseTermh e c (TmLamE _ t) = eraseTermh (succ e) (succ (headOr c 0) : c) t
eraseTermh e c (TmAppTm t t') = PureApp (eraseTermh e c t) (eraseTermh e c t')
eraseTermh e c (TmAppTmE t _) = eraseTermh e c t
eraseTermh e c (TmAppTp t _) = eraseTermh e c t
eraseTermh e c (TmIota t _ _) = eraseTermh e c t
eraseTermh e c (TmLetTm t t') = PureApp (PureLam (eraseTermh e (headOr c 0 : c) t')) (eraseTermh e c t)
eraseTermh e c (TmLetTmE _ t) = eraseTermh (succ e) (succ (headOr c 0) : c) t
eraseTermh e c (TmLetTp _ _ t) = eraseTermh (succ e) (succ (headOr c 0) : c) t
eraseTermh e c (IotaProj1 t) = eraseTermh e c t
eraseTermh e c (IotaProj2 t) = eraseTermh e c t
eraseTermh e c (Beta _ t) = erasePureTermh e c t
eraseTermh e c (Sigma t) = eraseTermh e c t
eraseTermh e c (Delta _ t) = eraseTermh e c t
eraseTermh e c (Rho _ _ t) = eraseTermh e c t
eraseTermh e c (Phi _ _ t) = erasePureTermh e c t
eraseTerm = eraseTermh 0 []

eraseTypeh e c (TpVar k) = TpVar (if k < length c then k + (c !! k) - head c else k - e)
eraseTypeh e c (TpRef v) = TpRef v
eraseTypeh e c (TpLam tk tp) = TpLam (eraseTpKdh e c tk) (eraseTypeh e (headOr c 0 : c) tp)
eraseTypeh e c (TpAll tk tp) = TpAll (eraseTpKdh e c tk) (eraseTypeh e (headOr c 0 : c) tp)
eraseTypeh e c (TpPi tp tp') = TpPi (eraseTypeh e c tp) (eraseTypeh e (headOr c 0 : c) tp')
eraseTypeh e c (TpEq tm tm') = TpEq (erasePureTermh e c tm) (erasePureTermh e c tm')
eraseTypeh e c (TpAppTp tp tp') = TpAppTp (eraseTypeh e c tp) (eraseTypeh e c tp')
eraseTypeh e c (TpAppTm tp tm) = TpAppTm (eraseTypeh e c tp) (eraseTermh e c tm)
eraseTypeh e c (TpIota tp tp') = TpIota (eraseTypeh e c tp) (eraseTypeh e (headOr c 0 : c) tp')
eraseType = eraseTypeh 0 []

eraseKindh e c Star = Star
eraseKindh e c (KdPi tk kd) = KdPi (eraseTpKdh e c tk) (eraseKindh e (headOr c 0 : c) kd)
eraseKind = eraseKindh 0 []

eraseTpKdh e c (TpKdTp tp) = TpKdTp (eraseTypeh e c tp)
eraseTpKdh e c (TpKdKd kd) = TpKdKd (eraseKindh e c kd)
eraseTpKd = eraseTpKdh 0 []

freeInTerm = h 0 . eraseTerm where
  h i (PureVar j) = i == j
  h i (PureRef v) = False
  h i (PureApp tm tm') = h i tm || h i tm'
  h i (PureLam tm) = h (succ i) tm

deltaTermh r d (PureVar j)      = PureVar (if j >= r then j + d else j)
deltaTermh r d (PureRef v)      = PureRef v
deltaTermh r d (PureApp tm tm') = PureApp (deltaTermh r d tm) (deltaTermh r d tm')
deltaTermh r d (PureLam tm)     = PureLam (deltaTermh (succ r) d tm)

deltaTypeh r d (TpVar j)        = TpVar (if j >= r then j + d else j)
deltaTypeh r d (TpRef v)        = TpRef v
deltaTypeh r d (TpLam tk tp) = TpLam (deltaTpKdh r d tk) (deltaTypeh (succ r) d tp)
deltaTypeh r d (TpAll tk tp)    = TpAll    (deltaTpKdh r d tk) (deltaTypeh (succ r) d tp)
deltaTypeh r d (TpPi tp tp')    = TpPi     (deltaTypeh r d tp) (deltaTypeh (succ r) d tp')
deltaTypeh r d (TpIota tp tp')  = TpIota   (deltaTypeh r d tp) (deltaTypeh (succ r) d tp')
deltaTypeh r d (TpEq tm tm')    = TpEq     (deltaTermh r d tm) (deltaTermh r        d tm')
deltaTypeh r d (TpAppTp tp tp') = TpAppTp  (deltaTypeh r d tp) (deltaTypeh r        d tp')
deltaTypeh r d (TpAppTm tp tm)  = TpAppTm  (deltaTypeh r d tp) (deltaTermh r        d tm)

deltaKindh r d Star = Star
deltaKindh r d (KdPi tk kd) = KdPi (deltaTpKdh r d tk) (deltaKindh (succ r) d kd)

deltaTpKdh r d (TpKdTp tp) = TpKdTp (deltaTypeh r d tp)
deltaTpKdh r d (TpKdKd kd) = TpKdKd (deltaKindh r d kd)

substTermh i z (PureVar j) = case compare j i of
  LT -> PureVar j
  EQ -> ctxtDeclElim (deltaTerm i) (const $ PureVar j) (const $ PureVar j) z
  GT -> PureVar (pred j)
substTermh i z (PureRef v)      = PureRef v
substTermh i z (PureApp tm tm') = PureApp (substTermh i z tm) (substTermh i z tm')
substTermh i z (PureLam tm)     = PureLam (substTermh (succ i) z tm)


substTypeh i z (TpVar j) = case compare j i of
  LT -> TpVar j
  EQ -> ctxtDeclElim (const $ TpVar j) (deltaType i) (const $ TpVar j) z
  GT -> TpVar (pred j)
substTypeh i z (TpRef v)        = TpRef v
substTypeh i z (TpLam tk tp) = TpLam (substTpKdh i z tk) (substTypeh (succ i) z tp)
substTypeh i z (TpAll tk tp)    = TpAll    (substTpKdh i z tk) (substTypeh (succ i) z tp)
substTypeh i z (TpPi tp tp')    = TpPi     (substTypeh i z tp) (substTypeh (succ i) z tp')
substTypeh i z (TpIota tp tp')  = TpIota   (substTypeh i z tp) (substTypeh (succ i) z tp')
substTypeh i z (TpEq tm tm')    = TpEq     (substTermh i z tm) (substTermh i        z tm')
substTypeh i z (TpAppTp tp tp') = TpAppTp  (substTypeh i z tp) (substTypeh i        z tp')
substTypeh i z (TpAppTm tp tm)  = TpAppTm  (substTypeh i z tp) (substTermh i        z tm)

substKindh i z Star = Star
substKindh i z (KdPi tk kd) = KdPi (substTpKdh i z tk) (substKindh (succ i) z kd)

substTpKdh i z = tkElim (TpKdTp . substTypeh i z) (TpKdKd . substKindh i z)


--hnfTermh :: Int -> Ctxt -> PureTerm -> PureTerm
hnfTermh i (Ctxt decls _ _ _) (PureVar j)
  | j >= i && j < i + length decls = ctxtDeclElim (deltaTerm j) (const $ PureVar j) (const $ PureVar j) (decls !! (j - i))
  | otherwise = PureVar j
hnfTermh i (Ctxt _ _ defs _) (PureRef v) =
  maybe (PureRef v) (ctxtDefElim const (\ _ _ -> PureRef v)) (trieLookup defs v)
hnfTermh i c (PureApp tm tm') =
  case hnfTermh i c tm of
    (PureLam btm) -> hnfTermh i c (substTerm (TermDecl tm') btm)
    htm -> PureApp htm tm'
hnfTermh i c (PureLam tm) = PureLam (hnfTermh (succ i) c tm)

hnfTypeh i (Ctxt decls _ _ _) (TpVar j)
  | j >= i && j < i + length decls = ctxtDeclElim (const $ TpVar j) (deltaType j) (const $ TpVar j) (decls !! (j - i))
  | otherwise = TpVar j
hnfTypeh i (Ctxt _ _ defs _) (TpRef v) = 
  maybe (TpRef v) (ctxtDefElim (\ _ _ -> TpRef v) const) (trieLookup defs v)
hnfTypeh i c (TpLam tk tp) = TpLam tk (hnfTypeh (succ i) c tp)
hnfTypeh i c (TpAll tk tp)    = TpAll tk (hnfTypeh (succ i) c tp)
hnfTypeh i c (TpPi tp tp')    = TpPi tp (hnfTypeh (succ i) c tp')
hnfTypeh i c (TpIota tp tp')  = TpIota tp tp'
hnfTypeh i c (TpEq tm tm')    = TpEq tm tm'
hnfTypeh i c (TpAppTp tp tp') =
  case hnfTypeh i c tp of
    (TpLam (TpKdKd _) btp) -> hnfTypeh i c (substType (TypeDecl tp') btp)
    htp -> TpAppTp htp tp'
hnfTypeh i c (TpAppTm tp tm) =
  case hnfTypeh i c tp of
    (TpLam (TpKdTp _) btp) -> hnfTypeh i c (substType (TermDecl tm) btp)
    htp -> TpAppTm htp tm

hnfKindh i c k = k

hnfTpKdh i c = tkElim (TpKdTp . hnfTypeh i c) (TpKdKd . hnfKindh i c)


{-


hnfTermh i c (PureVar j)
  | j >= i && j < i + length decls = ctxtDeclElim (deltaTerm i) (const $ PureVar j) (const $ PureVar j) (decls !! (j - i))
  | j < i = PureVar j
  | j >= i + length decls && j < i + length decls + length lets = ctxtDeclElim (deltaTerm (i - length decls)) (const $ PureVar j) (const $ PureVar j) (decls !! (j - i - length decls)) -- PureVar (j - length decls)
  | j >= i + length decls + length lets = PureVar (j - length decls)
hnfTermh u i decls lets defs (PureRef v) = maybe (PureRef v) id (trieLookup defs v >>= ctxtDefElim (const . Just) (\ _ _ -> Nothing))
hnfTermh False i decls lets defs (PureApp tm tm') = PureApp (hnfTermh False i decls lets defs tm) (hnfTermh False i decls lets defs tm')
hnfTermh True i decls lets defs (PureApp tm tm') = case hnfTermh True i decls lets defs tm of
  (PureLam tm'') -> hnfTermh True 0 (TermDecl (hnfTermh True i decls lets defs tm') : []) lets defs tm''
  tm'' -> PureApp tm'' (hnfTermh False i decls lets defs tm')
hnfTermh u i decls lets defs (PureLam tm) = PureLam (hnfTermh u (succ i) decls lets defs tm)

hnfTypeh u i decls lets defs (TpVar j)
  | j >= i && j < i + length decls = ctxtDeclElim (const $ TpVar j) (deltaType i) (const $ TpVar j) (decls !! (j - i))
  | j < i = TpVar j
  | j >= i + length decls = TpVar (j - length decls)
hnfTypeh u i decls lets defs (TpRef v) = maybe (TpRef v) id (trieLookup defs v >>= ctxtDefElim (\ _ _ -> Nothing) (const . Just))
hnfTypeh u i decls lets defs (TpLam tk tp) = TpLam (hnfTpKdh False i decls lets defs tk) (hnfTypeh u (succ i) decls lets defs tp)
hnfTypeh u i decls lets defs (TpAll tk tp) = TpAll (hnfTpKdh False i decls lets defs tk) (hnfTypeh u (succ i) decls lets defs tp)
hnfTypeh u i decls lets defs (TpPi tp tp') = TpPi (hnfTypeh False i decls lets defs tp) (hnfTypeh u (succ i) decls lets defs tp')
hnfTypeh u i decls lets defs (TpEq tm tm') = TpEq (hnfTermh False i decls lets defs tm) (hnfTermh False i decls lets defs tm')
hnfTypeh False i decls lets defs (TpAppTp tp tp') = TpAppTp (hnfTypeh False i decls lets defs tp) (hnfTypeh False i decls lets defs tp')
hnfTypeh False i decls lets defs (TpAppTm tp tm) = TpAppTm (hnfTypeh False i decls lets defs tp) (hnfTermh False i decls lets defs tm)
hnfTypeh True i decls lets defs (TpAppTp tp tp') = case hnfTypeh True i decls lets defs tp of
  (TpLam (TpKdKd _) tp'') -> hnfTypeh True 0 (TypeDecl (hnfTypeh True i decls lets defs tp') : []) lets defs tp''
  tp'' -> TpAppTp tp'' (hnfTypeh False i decls lets defs tp')
hnfTypeh True i decls lets defs (TpAppTm tp tm) = case hnfTypeh True i decls lets defs tp of
  (TpLam (TpKdTp _) tp') -> hnfTypeh True 0 (TermDecl (hnfTermh True i decls lets defs tm) : []) lets defs tp'
  tp' -> TpAppTm tp' (hnfTermh False i decls lets defs tm)
hnfTypeh u i decls lets defs (TpIota tp tp') = TpIota (hnfTypeh False i decls lets defs tp) (hnfTypeh False (succ i) decls lets defs tp')

hnfKindh u i decls lets defs Star = Star
hnfKindh u i decls lets defs (KdPi tk kd) = KdPi (hnfTpKdh False i decls lets defs tk) (hnfKindh u (succ i) decls lets defs kd)

hnfTpKdh u i decls lets defs (TpKdTp tp) = TpKdTp (hnfTypeh u i decls lets defs tp)
hnfTpKdh u i decls lets defs (TpKdKd kd) = TpKdKd (hnfKindh u i decls lets defs kd)
-}

convTermh c (PureVar i1) (PureVar i2) = i1 == i2
convTermh c (PureRef v1) (PureRef v2) = v1 == v2
convTermh c (PureApp tm1 tm1') (PureApp tm2 tm2') = convTermh c tm1 tm2 && convTerm c tm1' tm2'
convTermh c (PureLam tm1) (PureLam tm2) = convTermh (ctxtDecl c termDecl) tm1 tm2
convTermh c (PureLam tm1) tm2 = convTerm (ctxtDecl c termDecl) tm1 (PureApp (deltaTerm 1 tm2) (PureVar 0))
convTermh c tm1 (PureLam tm2) = convTerm (ctxtDecl c termDecl) (PureApp (deltaTerm 1 tm1) (PureVar 0)) tm2
convTermh _ _ _ = False

convTypeh c (TpVar i1) (TpVar i2) = i1 == i2
convTypeh c (TpRef v1) (TpRef v2) = v1 == v2
convTypeh c (TpAll tk1 tp1) (TpAll tk2 tp2) =
  convTpKd c tk1 tk2 && convTypeh (ctxtDecl c (if tkIs tk1 then termDecl else typeDecl)) tp1 tp2
convTypeh c (TpLam tk1 tp1) (TpLam tk2 tp2) =
  convTpKd c tk1 tk2 && convTypeh (ctxtDecl c (if tkIs tk1 then termDecl else typeDecl)) tp1 tp2
convTypeh c (TpPi tp1 tp1') (TpPi tp2 tp2') =
  convType c tp1 tp2 && convTypeh (ctxtDecl c termDecl) tp1' tp2'
convTypeh c (TpIota tp1 tp1') (TpIota tp2 tp2') =
  convType c tp1 tp2 && convType (ctxtDecl c termDecl) tp1' tp2'
convTypeh c (TpEq tm1 tm1') (TpEq tm2 tm2') = convTerm c tm1 tm2 && convTerm c tm1' tm2'
convTypeh c (TpAppTp tp1 tp1') (TpAppTp tp2 tp2') =
  convTypeh c tp1 tp2 && convType c tp1' tp2'
convTypeh c (TpAppTm tp1 tm1) (TpAppTm tp2 tm2) =
  convTypeh c tp1 tp2 && convTerm c tm1 tm2
convTypeh _ _ _ = False

convKindh c Star Star = True
convKindh c (KdPi tk kd) (KdPi tk' kd') =
  convTpKd c tk tk' && convKind (ctxtDecl c (if tkIs tk then termDecl else typeDecl)) kd kd'
convKindh c _ _ = False

convTpKdh c (TpKdTp tp) (TpKdTp tp') = convTypeh c tp tp'
convTpKdh c (TpKdKd kd) (TpKdKd kd') = convKindh c kd kd'
convTpKdh c _ _ = False


deltaTerm = deltaTermh 0
deltaType = deltaTypeh 0
deltaKind = deltaKindh 0
deltaTpKd = deltaTpKdh 0

deltaDecl i = ctxtDeclElim
  (TermDecl . deltaTerm i)
  (TypeDecl . deltaType i)
  (KindDecl . deltaKind i)

--hnfTerm (Ctxt decls types defs scope) = hnfTermh True 0 [] decls defs -- (length decls) decls defs
--hnfType (Ctxt decls types defs scope) = hnfTypeh True 0 [] decls defs
--hnfKind (Ctxt decls types defs scope) = hnfKindh True 0 [] decls defs
--hnfTpKd (Ctxt decls types defs scope) = hnfTpKdh True 0 [] decls defs
hnfTerm = hnfTermh 0
hnfType = hnfTypeh 0
hnfKind = hnfKindh 0
hnfTpKd = hnfTpKdh 0


hnfeTerm c = hnfTerm c . eraseTerm
hnfeType c = hnfType c . eraseType
hnfeKind c = hnfKind c . eraseKind
hnfeTpKd c = hnfTpKd c . eraseTpKd

--substTerm decl = hnfTermh False 0 [decl] [] emptyTrie
--substType decl = hnfTypeh False 0 [decl] [] emptyTrie
--substKind decl = hnfKindh False 0 [decl] [] emptyTrie
--substTpKd decl = hnfTpKdh False 0 [decl] [] emptyTrie
substTerm = substTermh 0
substType = substTypeh 0
substKind = substKindh 0
substTpKd = substTpKdh 0

convTerm c tm tm' = convTermh c tm tm' || convTermh c (hnfTerm c tm) (hnfTerm c tm')
convType c tp tp' = convTypeh c tp tp' || convTypeh c (hnfType c tp) (hnfType c tp')
convKind c kd kd' = convKindh c kd kd' || convKindh c (hnfKind c kd) (hnfKind c kd')
convTpKd c tk tk' = convTpKdh c tk tk' || convTpKdh c (hnfTpKd c tk) (hnfTpKd c tk')
