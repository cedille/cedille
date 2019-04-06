module Check where
import Types
import Trie
import Norm

ifM b = if b then Just () else Nothing

--synthTerm :: Ctxt -> Term -> Maybe PrType
synthTerm c (TmVar i) =
  ctxtLookupDeclType c i >>=
  either Just (const Nothing)
synthTerm c (TmRef v) =
  fmap snd $ ctxtLookupTermDef c v
synthTerm c (TmLam tp tm) =
  checkType c tp >>
  synthTerm (ctxtDeclType c tmDecl (Left $ hnfeType c tp)) tm >>=
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
      Just (substType (Left (eraseTerm tm')) cod)
    _ -> Nothing
synthTerm c (TmAppTmE tm tm') =
  synthTerm c tm' >>= \ tp' ->
  synthTerm c tm >>= \ tp -> case hnfType c tp of
    (TpAll (Left dom) cod) ->
      ifM (convType c dom tp') >>
      Just (substType (Left (eraseTerm tm')) cod)
    _ -> Nothing
synthTerm c (TmAppTp tm tp) =
  synthType c tp >>= \ kd ->
  synthTerm c tm >>= \ all -> case hnfType c all of
    (TpAll (Right dom) cod) ->
      ifM (convKind c dom kd) >>
      Just (substType (Right (eraseType tp)) cod)
    _ -> Nothing
synthTerm c (TmIota tm tm' gd) =
  synthTerm c tm >>= \ tp ->
  synthTerm c tm' >>= \ tp' ->
  checkType (ctxtDeclType c tmDecl $ Left $ hnfType c tp) gd >>
  ifM (convType c (substType (Left (eraseTerm tm)) $ eraseType gd) tp') >>
  ifM (convTerm c (eraseTerm tm) (eraseTerm tm')) >>
  Just (TpIota tp $ eraseType gd)
synthTerm c (TmLetTm tm' tm) =
  synthTerm c tm' >>= \ tp' ->
  synthTerm (ctxtDeclType c (Left $ deltaTerm 1 $ hnfeTerm c tm') $ Left $ hnfType c tp') tm >>=
  Just . substType (Left $ eraseTerm tm')
synthTerm c (TmLetTmE tm' tm) =
  synthTerm c tm' >>= \ tp ->
  ifM (not $ freeInTerm tm) >>
  synthTerm (ctxtDeclType c (Left $ deltaTerm 1 $ hnfeTerm c tm') $ Left $ hnfType c tp) tm >>=
  Just . substType (Left $ eraseTerm tm')
synthTerm c (TmLetTp kd tp tm) =
  synthType c tp >>= \ kd' ->
  ifM (convKind c (eraseKind kd) kd') >>
  ifM (not $ freeInTerm tm) >>
  synthTerm (ctxtDeclType c (Right $ deltaType 1 $ hnfeType c tp) $ Right $ hnfeKind c kd) tm >>=
  Just . substType (Right $ eraseType tp)
synthTerm c (TmProj1 tm) =
  synthTerm c tm >>= \ tp -> case hnfType c tp of
    (TpIota tp1 tp2) -> Just tp1
    _ -> Nothing
synthTerm c (TmProj2 tm) =
  synthTerm c tm >>= \ tp -> case hnfType c tp of
    (TpIota tp1 tp2) ->
      Just (substType (Left (hnfeTerm c tm)) tp2)
    _ -> Nothing
synthTerm c (TmBeta tm tm') =
  validTerm c tm >>
  validTerm c tm' >>
  Just (TpEq tm tm)
synthTerm c (TmSigma tm) =
  synthTerm c tm >>= \ tp -> case hnfType c tp of
    (TpEq l r) -> Just (TpEq r l)
    _ -> Nothing
synthTerm c (TmDelta tp tm) =
  validType c tp >>
  synthTerm c tm >>= \ tp' -> case hnfType c tp' of
    (TpEq l r) ->
      ifM (convTerm c l (PrLam $ PrLam $ PrVar 1)) >>
      ifM (convTerm c r (PrLam $ PrLam $ PrVar 0)) >>
      Just tp
    _ -> Nothing
synthTerm c (TmRho pf gd tm) =
  validType (ctxtDecl c tmDecl) gd >>
  synthTerm c tm >>= \ tp ->
  synthTerm c pf >>= \ eq -> case hnfType c eq of
    (TpEq l r) ->
      ifM (convType c (substType (Left r) gd) tp) >>
      Just (substType (Left l) gd)
    _ -> Nothing
synthTerm c (TmPhi tm tm' tm'') =
  validTerm c tm'' >>
  synthTerm c tm >>= \ eq ->
  case hnfType c eq of
    TpEq l r ->
      ifM (convTerm c l (eraseTerm tm')) >>
      ifM (convTerm c r tm'') >>
      synthTerm c tm'
    _ -> Nothing

synthType c (TpVar i) =
  ctxtLookupDeclType c i >>=
  either (const Nothing) Just
synthType c (TpRef v) =
  fmap snd $ ctxtLookupTypeDef c v  
synthType c (TpLam tk tp) =
  checkTpKd c tk >>
  synthType (ctxtDeclTpKd c $ hnfeTpKd c tk) tp >>=
  Just . KdPi (eraseTpKd tk)
synthType c (TpAll tk tp) =
  checkTpKd c tk >>
  checkType (ctxtDeclTpKd c $ hnfeTpKd c tk) tp >>
  Just KdStar
synthType c (TpPi tp tp') =
  checkType c tp >>
  checkType (ctxtDeclType c tmDecl (Left $ hnfeType c tp)) tp' >>
  Just KdStar
synthType c (TpIota tp tp') =
  checkType c tp >>
  checkType (ctxtDeclType c tmDecl (Left $ hnfeType c tp)) tp' >>
  Just KdStar
synthType c (TpEq tm tm') =
  validTerm c tm >>
  validTerm c tm' >>
  Just KdStar
synthType c (TpAppTp tp tp') =
  synthType c tp' >>= \ kd' ->
  synthType c tp >>= \ kd -> case hnfKind c kd of
    (KdPi (Right dom) cod) ->
      ifM (convKind c dom kd') >>
      Just (substKind (Right $ hnfeType c tp') cod)
    _ -> Nothing
synthType c (TpAppTm tp tm) =
  synthTerm c tm >>= \ tp' ->
  synthType c tp >>= \ kd -> case hnfKind c kd of
    (KdPi (Left dom) cod) ->
      ifM (convType c dom tp') >>
      Just (substKind (Left $ hnfeTerm c tm) cod)
    _ -> Nothing

synthKind c KdStar = Just ()
synthKind c (KdPi tk kd) =
  checkTpKd c tk >>
  synthKind (ctxtDeclTpKd c $ hnfeTpKd c tk) kd

synthTpKd c = either
  (\ tp -> synthType c tp >>= Just . Just)
  (\ kd -> synthKind c kd >> Just Nothing)
  

-- Check against kind Star
checkType c tp =
  synthType c tp >>= \ kd ->
  ifM (convKind c kd KdStar)

checkTpKd c tk =
  synthTpKd c tk >>=
  maybe (Just ()) (ifM . convKind c KdStar)

-- Does the pure expression use only locally bound and global variables?
validTerm (Ctxt decls types defs scope) (PrVar i) = ifM (i < length decls)
validTerm c (PrRef v) = ctxtLookupTermDef c v >> Just ()
validTerm c (PrApp tm tm') = validTerm c tm >> validTerm c tm'
validTerm c (PrLam tm) = validTerm (ctxtDecl c tmDecl) tm

validType (Ctxt decls types defs scope) (TpVar i) = ifM (i < length decls)
validType c (TpRef v) = ctxtLookupTypeDef c v >> Just ()
validType c (TpLam tk tp) = validTpKd c tk >> validType (ctxtDecl c (tkDecl tk)) tp
validType c (TpAll tk tp) = validTpKd c tk >> validType (ctxtDecl c (tkDecl tk)) tp
validType c (TpPi tp tp') = validType c tp >> validType (ctxtDecl c tmDecl) tp'
validType c (TpIota tp tp') = validType c tp >> validType (ctxtDecl c tmDecl) tp'
validType c (TpEq tm tm') = validTerm c tm >> validTerm c tm'
validType c (TpAppTp tp tp') = validType c tp >> validType c tp'
validType c (TpAppTm tp tm) = validType c tp >> validTerm c tm

validKind c KdStar = Just ()
validKind c (KdPi tk kd) = validTpKd c tk >> validKind (ctxtDecl c (tkDecl tk)) kd

validTpKd c = either (validType c) (validKind c)
