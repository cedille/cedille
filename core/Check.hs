module Check where
import Types
import Trie
import Norm

--synthTerm :: Ctxt -> Term -> Maybe PureType
synthTerm c (TmVar i) =
  ctxtLookupDeclType c i >>=
  ctxtDeclElim (const Nothing) Just (const Nothing)
synthTerm c (TmRef v) =
  fmap snd $ ctxtLookupTermDef c v
synthTerm c (TmLam tp tm) =
  checkType c tp >>
  synthTerm (ctxtDeclType c termDecl (TypeDecl $ hnfeType c tp)) tm >>=
  Just . TpPi (eraseType tp)
synthTerm c (TmLamE tk tm) =
  checkTpKd c tk >>
  ifM (not $ freeInTerm tm) >>
  synthTerm (ctxtDeclTpKd c $ hnfeTpKd c tk) tm >>=
  Just . TpAll (eraseTpKd tk)
synthTerm c (TmAppTm tm tm') =
  synthTerm c tm' >>= \ tp' ->
  synthTerm c tm >>= \ tp -> case hnfType c tp of
    (TpPi dom cod) ->
      ifM (convType c dom tp') >>
      Just (substType (TermDecl (eraseTerm tm')) cod)
    _ -> Nothing
synthTerm c (TmAppTmE tm tm') =
  synthTerm c tm' >>= \ tp' ->
  synthTerm c tm >>= \ tp -> case hnfType c tp of
    (TpAll (TpKdTp dom) cod) ->
      ifM (convType c dom tp') >>
      Just (substType (TermDecl (eraseTerm tm')) cod)
    _ -> Nothing
synthTerm c (TmAppTp tm tp) =
  synthType c tp >>= \ kd ->
  synthTerm c tm >>= \ all -> case hnfType c all of
    (TpAll (TpKdKd dom) cod) ->
      ifM (convKind c dom kd) >>
      Just (substType (TypeDecl (eraseType tp)) cod)
    _ -> Nothing
synthTerm c (TmIota tm tm' gd) =
  synthTerm c tm >>= \ tp ->
  synthTerm c tm' >>= \ tp' ->
  checkType (ctxtDeclType c termDecl $ TypeDecl $ hnfType c tp) gd >>
  ifM (convType c (substType (TermDecl (eraseTerm tm)) $ eraseType gd) tp') >>
  ifM (convTerm c (eraseTerm tm) (eraseTerm tm')) >>
  Just (TpIota tp $ eraseType gd)
synthTerm c (TmLetTm tm' tm) =
  synthTerm c tm' >>= \ tp' ->
  synthTerm (ctxtDeclType c (TermDecl $ deltaTerm 1 $ hnfeTerm c tm') $ TypeDecl $ hnfType c tp') tm >>=
  Just . substType (TermDecl $ eraseTerm tm')
synthTerm c (TmLetTmE tm' tm) =
  synthTerm c tm' >>= \ tp ->
  ifM (not $ freeInTerm tm) >>
  synthTerm (ctxtDeclType c (TermDecl $ deltaTerm 1 $ hnfeTerm c tm') $ TypeDecl $ hnfType c tp) tm >>=
  Just . substType (TermDecl $ eraseTerm tm')
synthTerm c (TmLetTp kd tp tm) =
  synthType c tp >>= \ kd' ->
  ifM (convKind c (eraseKind kd) kd') >>
  ifM (not $ freeInTerm tm) >>
  synthTerm (ctxtDeclType c (TypeDecl $ deltaType 1 $ hnfeType c tp) $ KindDecl $ hnfeKind c kd) tm >>=
  Just . substType (TypeDecl $ eraseType tp)
synthTerm c (IotaProj1 tm) =
  synthTerm c tm >>= \ tp -> case hnfType c tp of
    (TpIota tp1 tp2) -> Just tp1
    _ -> Nothing
synthTerm c (IotaProj2 tm) =
  synthTerm c tm >>= \ tp -> case hnfType c tp of
    (TpIota tp1 tp2) ->
      Just (substType (TermDecl (hnfeTerm c tm)) tp2)
    _ -> Nothing
synthTerm c (Beta tm tm') =
  validTerm c tm >>
  validTerm c tm' >>
  Just (TpEq tm tm)
synthTerm c (Sigma tm) =
  synthTerm c tm >>= \ tp -> case hnfType c tp of
    (TpEq l r) -> Just (TpEq r l)
    _ -> Nothing
synthTerm c (Delta tp tm) =
  validType c tp >>
  synthTerm c tm >>= \ tp' -> case hnfType c tp' of
    (TpEq l r) ->
      ifM (convTerm c l (PureLam $ PureLam $ PureVar 1)) >>
      ifM (convTerm c r (PureLam $ PureLam $ PureVar 0)) >>
      Just (hnfType c tp)
    _ -> Nothing
synthTerm c (Rho pf gd tm) =
  validType (ctxtDecl c termDecl) gd >>
  synthTerm c tm >>= \ tp ->
  synthTerm c pf >>= \ eq -> case hnfType c eq of
    (TpEq l r) ->
      ifM (convType c (substType (TermDecl r) gd) tp) >>
      Just (substType (TermDecl l) gd)
    _ -> Nothing
synthTerm c (Phi tm tm' tm'') =
  validTerm c tm'' >>
  synthTerm c tm >>= \ eq ->
  case hnfType c eq of
    TpEq l r ->
      ifM (convTerm c l $ eraseTerm tm') >>
      ifM (convTerm c r tm'') >>
      synthTerm c tm'
    _ -> Nothing

synthType c (TpVar i) =
  ctxtLookupDeclType c i >>=
  ctxtDeclElim (const Nothing) (const Nothing) Just
synthType c (TpRef v) =
  fmap snd $ ctxtLookupTypeDef c v  
synthType c (TpLam tk tp) =
  checkTpKd c tk >>
  synthType (ctxtDeclTpKd c $ hnfeTpKd c tk) tp >>=
  Just . KdPi (eraseTpKd tk)
synthType c (TpAll tk tp) =
  checkTpKd c tk >>
  checkType (ctxtDeclTpKd c $ hnfeTpKd c tk) tp >>
  Just Star
synthType c (TpPi tp tp') =
  checkType c tp >>
  checkType (ctxtDeclType c termDecl (TypeDecl $ hnfeType c tp)) tp' >>
  Just Star
synthType c (TpIota tp tp') =
  checkType c tp >>
  checkType (ctxtDeclType c termDecl (TypeDecl $ hnfeType c tp)) tp' >>
  Just Star
synthType c (TpEq tm tm') =
  validTerm c tm >>
  validTerm c tm' >>
  Just Star
synthType c (TpAppTp tp tp') =
  synthType c tp' >>= \ kd' ->
  synthType c tp >>= \ kd -> case hnfKind c kd of
    (KdPi (TpKdKd dom) cod) ->
      ifM (convKind c dom kd') >>
      Just (substKind (TypeDecl $ hnfeType c tp') cod)
    _ -> Nothing
synthType c (TpAppTm tp tm) =
  synthTerm c tm >>= \ tp' ->
  synthType c tp >>= \ kd -> case hnfKind c kd of
    (KdPi (TpKdTp dom) cod) ->
      ifM (convType c dom tp') >>
      Just (substKind (TermDecl $ hnfeTerm c tm) cod)
    _ -> Nothing

synthKind c Star = Just ()
synthKind c (KdPi tk kd) =
  synthTpKd c tk >>
  synthKind (ctxtDeclTpKd c $ hnfeTpKd c tk) kd

synthTpKd c = tkElim
  (\ tp -> synthType c tp >>= Just . Just)
  (\ kd -> synthKind c kd >> Just Nothing)
  
-- Checks tp against kind Star
checkType c tp =
  synthType c tp >>= \ kd ->
  ifM (convKind c kd Star)

checkTpKd c tk =
  synthTpKd c tk >>=
  maybe (Just ()) (ifM . convKind c Star)

validTerm (Ctxt decls types defs scope) (PureVar i) = ifM (i < length decls)
validTerm c (PureRef v) = ctxtLookupTermDef c v >> Just ()
validTerm c (PureApp tm tm') = validTerm c tm >> validTerm c tm'
validTerm c (PureLam tm) = validTerm (ctxtDecl c termDecl) tm

validType (Ctxt decls types defs scope) (TpVar i) =
  ifM (i < length decls)
validType c (TpRef v) =
  ctxtLookupTypeDef c v >> Just ()
validType c (TpLam tk tp) =
  validTpKd c tk >>
  validType (ctxtDecl c (tkElim (const termDecl) (const typeDecl) tk)) tp
validType c (TpAll tk tp) =
  validTpKd c tk >>
  validType (ctxtDecl c (tkElim (const termDecl) (const typeDecl) tk)) tp
validType c (TpPi tp tp') =
  validType c tp >>
  validType (ctxtDecl c termDecl) tp'
validType c (TpIota tp tp') =
  validType c tp >>
  validType (ctxtDecl c termDecl) tp'
validType c (TpEq tm tm') =
  validTerm c tm >>
  validTerm c tm'
validType c (TpAppTp tp tp') =
  validType c tp >>
  validType c tp'
validType c (TpAppTm tp tm) =
  validType c tp >>
  validTerm c tm

validKind c Star = Just ()
validKind c (KdPi tk kd) =
  validTpKd c tk >>
  validKind (ctxtDecl c (tkElim (const termDecl) (const typeDecl) tk)) kd

validTpKd c = tkElim (validType c) (validKind c)
