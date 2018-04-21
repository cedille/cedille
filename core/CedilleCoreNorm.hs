module CedilleCoreNorm where
import qualified Data.Map as Map
import CedilleCoreTypes
import CedilleCoreCtxt

--eraseTerm :: Term -> PureTerm
eraseTerm (TmVar v) = PureVar v
eraseTerm (TmLambda v tp tm) = PureLambda v (eraseTerm tm)
eraseTerm (TmAppTm tm tm') = PureApp (eraseTerm tm) (eraseTerm tm')
eraseTerm (TmLambdaE v c tm) = eraseTerm tm
eraseTerm (TmAppTmE tm tm') = eraseTerm tm
eraseTerm (TmAppTp tm tp) = eraseTerm tm
eraseTerm (IotaPair tm1 tm2 v tp) = eraseTerm tm1
eraseTerm (IotaProj1 tm) = eraseTerm tm
eraseTerm (IotaProj2 tm) = eraseTerm tm
eraseTerm (Beta pt pt') = pt'
eraseTerm (Sigma tm) = eraseTerm tm
eraseTerm (Delta tp tm) = eraseTerm tm
eraseTerm (Rho tm v tp tm') = eraseTerm tm'
eraseTerm (Phi tm tm' pt) = pt

--eraseType :: Type -> PureType
eraseType (TpVar v) = TpVar v
eraseType (TpLambda v tk tp) = TpLambda v (eraseTk tk) (eraseType tp)
eraseType (TpAll v tk tp) = TpAll v (eraseTk tk) (eraseType tp)
eraseType (TpPi v tp tp') = TpPi v (eraseType tp) (eraseType tp')
eraseType (TpEq ptm ptm') = TpEq ptm ptm'
eraseType (TpAppTp tp tp') = TpAppTp (eraseType tp) (eraseType tp')
eraseType (TpAppTm tp tm) = TpAppTm (eraseType tp) (eraseTerm tm)
eraseType (Iota v tp tp') = Iota v (eraseType tp) (eraseType tp')

--eraseKind :: Kind -> PureKind
eraseKind Star = Star
eraseKind (KdPi v tk kd) = KdPi v (eraseTk tk) (eraseKind kd)

--eraseTk :: Tk -> PureTk
eraseTk (Tkt tp) = Tkt (eraseType tp)
eraseTk (Tkk kd) = Tkk (eraseKind kd)

substTerm c (PureVar v) = maybe (PureVar (ctxtRep c v)) id (ctxtLookupInternalTerm c v)
substTerm c (PureApp tm tm') = PureApp (substTerm c tm) (substTerm c tm')
substTerm c (PureLambda v tm) = doRename' c v $ \ v' -> PureLambda v' (substTerm (ctxtRename c v v') tm)

substType c (TpVar v) = maybe (TpVar (ctxtRep c v)) id (ctxtLookupInternalType c v)
substType c (TpLambda v tk tp) =
  doRename' c v $ \ v' -> TpLambda v' (substTk c tk) (substType (ctxtRename c v v') tp)
substType c (TpAll v tk tp) =
  doRename' c v $ \ v' -> TpAll v' (substTk c tk) (substType (ctxtRename c v v') tp)
substType c (TpPi v tp tp') =
  doRename' c v $ \ v' -> TpPi v' (substType c tp) (substType (ctxtRename c v v') tp')
substType c (Iota v tp tp') =
  doRename' c v $ \ v' -> Iota v' (substType c tp) (substType (ctxtRename c v v') tp')
substType c (TpAppTp tp tp') = TpAppTp (substType c tp) (substType c tp')
substType c (TpAppTm tp tm) = TpAppTm (substType c tp) (substTerm c tm)
substType c (TpEq tm tm') = TpEq (substTerm c tm) (substTerm c tm')

substKind c Star = Star
substKind c (KdPi v tk kd) =
  doRename' c v $ \ v' -> KdPi v' (substTk c tk) (substKind (ctxtRename c v v') kd)

substTk c (Tkt tp) = Tkt $ substType c tp
substTk c (Tkk kd) = Tkk $ substKind c kd

--hnfTerm :: Ctxt -> PureTerm -> PureTerm
hnfTerm c (PureVar v) = maybe (PureVar (ctxtRep c v)) (substTerm c) (ctxtLookupTermVar c v)
hnfTerm c (PureApp tm tm') = case hnfTerm c tm of
  PureLambda v tm'' -> hnfTerm (ctxtInternalDef c v (Left (hnfTerm (ctxtRename c v v) tm'))) tm''
  tm'' -> PureApp tm'' (substTerm c tm')
hnfTerm c (PureLambda v tm) = doRename' c v $ \ v' ->
  let c' = ctxtRename c v v' in
  let tm' = hnfTerm c' tm in
  let etm = PureLambda v' tm' in case tm' of
    (PureApp htm atm) -> case hnfTerm c' atm of
      (PureVar v'') -> if v' == v'' then htm else etm
      _ -> etm
    _ -> etm

tkIsType (Tkt _) = True
tkIsType (Tkk _) = False
  
--hnfType :: Ctxt -> PureType -> PureType
hnfType c (TpVar v) = maybe (TpVar (ctxtRep c v)) (substType c) (ctxtLookupTypeVar c v)
hnfType c (TpLambda v tk tp) = doRename' c v $ \ v' ->
  let c' = ctxtRename c v v' in
  let tp' = hnfType c' tp in
  let tk' = substTk c tk in
  let etp = TpLambda v' tk' tp' in case tp' of
    (TpAppTp htp atp) -> case hnfType c' atp of
      (TpVar v'') -> if not (tkIsType tk) && v' == v'' then htp else etp
      _ -> etp
    (TpAppTm htp tm) -> case hnfTerm c' tm of
      (PureVar v'') -> if tkIsType tk && v' == v'' then htp else etp
      _ -> etp
    _ -> etp
hnfType c (TpAll v tk tp) =
  doRename' c v $ \ v' -> TpAll v' (substTk c tk) (hnfType (ctxtRename c v v') tp)
hnfType c (TpPi v tp tp') =
  doRename' c v $ \ v' -> TpPi v' (substType c tp) (hnfType (ctxtRename c v v') tp')
hnfType c (Iota v tp tp') =
  doRename' c v $ \ v' -> Iota v' (substType c tp) (substType (ctxtRename c v v') tp')
hnfType c (TpAppTp tp tp') = case hnfType c tp of
  TpLambda v (Tkk _) tp'' -> hnfType (ctxtInternalDef c v (Right (hnfType (ctxtRename c v v) tp'))) tp''
  tp'' -> TpAppTp tp'' (substType c tp')
hnfType c (TpAppTm tp tm) = case hnfType c tp of
  TpLambda v (Tkt _) tp' -> hnfType (ctxtInternalDef c v (Left (hnfTerm (ctxtRename c v v) tm))) tp'
  tp' -> TpAppTm tp' (substTerm c tm)
hnfType c (TpEq tm tm') = TpEq (substTerm c tm) (substTerm c tm')

--hnfKind :: Ctxt -> PureKind -> PureKind
hnfKind c Star = Star
hnfKind c (KdPi v tk kd) =
  doRename' c v $ \ v' -> KdPi v' (substTk c tk) (hnfKind (ctxtRename c v v') kd)

--hnfTk :: Ctxt -> PureTk -> PureTk
hnfTk c (Tkt tp) = Tkt (hnfType c tp)
hnfTk c (Tkk kd) = Tkk (hnfKind c kd)

convTerm c tm tm' = convTerm' c (hnfTerm c tm) (hnfTerm c tm')
convType c tp tp' = convType' c (hnfType c tp) (hnfType c tp')
convKind c kd kd' = convKind' c (hnfKind c kd) (hnfKind c kd')
convTk c tk tk' = convTk' c (hnfTk c tk) (hnfTk c tk')

--convTerm' :: Ctxt -> PureTerm -> PureTerm -> Bool
convTerm' c (PureVar v) (PureVar v') =
  ctxtRep c v == ctxtRep c v'
convTerm' c (PureLambda v tm) (PureLambda v' tm') = convTerm' (ctxtRename c v v') tm tm'
convTerm' c (PureApp tm tm') (PureApp tm'' tm''') = convTerm' c tm tm'' && convTerm c tm' tm'''
{-convTerm' c (PureLambda v (PureApp tm tmv)) tm' = case hnfTerm (ctxtRename c v v) tmv of
  (PureVar v') -> v == v' && convTerm' c tm tm'
  _ -> False
convTerm' c tm (PureLambda v (PureApp tm' tmv)) = case hnfTerm (ctxtRename c v v) tmv of
  (PureVar v') -> v == v' && convTerm' c tm tm'
  _ -> False-}
convTerm' _ _ _ = False

--convType' :: Ctxt -> PureType -> PureType -> Bool
convType' c (TpVar v) (TpVar v') = ctxtRep c v == ctxtRep c v'
convType' c (TpLambda v tk tp) (TpLambda v' tk' tp') = convTk c tk tk' && convType' (ctxtRename c v v') tp tp'
convType' c (TpAll v tk tp) (TpAll v' tk' tp') = convTk c tk tk' && convType' (ctxtRename c v v') tp tp'
convType' c (TpPi v tp tp') (TpPi v' tp'' tp''') = convType c tp tp'' && convType' (ctxtRename c v v') tp' tp'''
convType' c (Iota v tp tp') (Iota v' tp'' tp''') = convType c tp tp'' && convType (ctxtRename c v v') tp' tp'''
convType' c (TpEq tm tm') (TpEq tm'' tm''') = convTerm c tm tm'' && convTerm c tm' tm'''
convType' c (TpAppTp tp tp') (TpAppTp tp'' tp''') = convType' c tp tp'' && convType c tp' tp'''
convType' c (TpAppTm tp tm) (TpAppTm tp' tm') = convType' c tp tp' && convTerm c tm tm'
{-convType' c (TpLambda v (Tkk _) (TpAppTp tp tpv)) tp' = case hnfType (ctxtRename c v v) tpv of
  (TpVar v') -> v == v' && convType' c tp tp'
  _ -> False
convType' c tp (TpLambda v (Tkk _) (TpAppTp tp' tpv)) = case hnfType (ctxtRename c v v) tpv of
  (TpVar v') -> v == v' && convType' c tp tp'
  _ -> False
convType' c (TpLambda v (Tkt _) (TpAppTm tp tmv)) tp' = case hnfTerm (ctxtRename c v v) tmv of
  (PureVar v') -> v == v' && convType' c tp tp'
  _ -> False
convType' c tp (TpLambda v (Tkt _) (TpAppTm tp' tmv)) = case hnfTerm (ctxtRename c v v) tmv of
  (PureVar v') -> v == v' && convType' c tp tp'
  _ -> False-}
convType' c tp tp' = False

--convKind' :: Ctxt -> PureKind -> PureKind -> Bool
convKind' c Star Star = True
convKind' c (KdPi v tk kd) (KdPi v' tk' kd') = convTk c tk tk' && convKind' (ctxtRename c v v') kd kd'

convTk' c (Tkt tp) (Tkt tp') = convType' c tp tp'
convTk' c (Tkk kd) (Tkk kd') = convKind' c kd kd'
convTk' c _ _ = False


--freeInPureTerm :: Var -> PureTerm -> Bool
freeInPureTerm v (PureVar v') = v == v'
freeInPureTerm v (PureApp tm tm') = freeInPureTerm v tm || freeInPureTerm v tm'
freeInPureTerm v (PureLambda v' tm) = not (v == v' || not (freeInPureTerm v tm))

--freeInTerm :: Var -> Term -> Bool
freeInTerm v (TmVar v') = v == v'
freeInTerm v (TmLambda v' tp tm) = not (v == v' || not (freeInTerm v tm || freeInType v tp))
freeInTerm v (TmAppTm tm tm') = freeInTerm v tm || freeInTerm v tm'
freeInTerm v (TmLambdaE v' tk tm) = not (v == v' || not (freeInTerm v tm || freeInTk v tk))
freeInTerm v (TmAppTmE tm tm') = freeInTerm v tm || freeInTerm v tm'
freeInTerm v (TmAppTp tm tp) = freeInTerm v tm || freeInType v tp
freeInTerm v (IotaPair tm1 tm2 v' tp) = freeInTerm v tm1 || freeInTerm v tm2 || not (v == v' || not (freeInType v tp))
freeInTerm v (IotaProj1 tm) = freeInTerm v tm
freeInTerm v (IotaProj2 tm) = freeInTerm v tm
freeInTerm v (Beta pt pt') = freeInPureTerm v pt || freeInPureTerm v pt'
freeInTerm v (Sigma tm) = freeInTerm v tm
freeInTerm v (Delta tp tm) = freeInPureType v tp || freeInTerm v tm
freeInTerm v (Rho tm v' tp tm') = freeInTerm v tm || freeInTerm v tm' || not (v == v' || not (freeInPureType v tp))
freeInTerm v (Phi tm tm' pt) = freeInTerm v tm || freeInTerm v tm' || freeInPureTerm v pt

freeInType = freeInType' freeInTerm
freeInPureType = freeInType' freeInPureTerm
freeInKind = freeInKind' freeInTerm
freeInPureKind = freeInKind' freeInPureTerm
freeInTk = freeInTk' freeInTerm
freeInPureTk = freeInTk' freeInPureTerm

--freeInType' :: (Var -> tm -> Bool) -> Var -> PrimType tm -> Bool
freeInType' f v (TpVar v') = v == v'
freeInType' f v (TpLambda v' tk tp) = not (v == v' || not (freeInTk' f v tk || freeInType' f v tp))
freeInType' f v (TpAll v' tk tp) = not (v == v' || not (freeInTk' f v tk || freeInType' f v tp))
freeInType' f v (TpPi v' tp tp') = not (v == v' || not (freeInType' f v tp || freeInType' f v tp'))
freeInType' f v (TpEq tm tm') = freeInPureTerm v tm || freeInPureTerm v tm'
freeInType' f v (TpAppTp tp tp') = freeInType' f v tp || freeInType' f v tp'
freeInType' f v (TpAppTm tp tm) = freeInType' f v tp || f v tm
freeInType' f v (Iota v' tp tp') = not (v == v' || not (freeInType' f v tp || freeInType' f v tp'))

--freeInKind' :: (Var -> tm -> Bool) -> Var -> PrimKind tm -> Bool
freeInKind' f v Star = False
freeInKind' f v (KdPi v' tk kd) = not (v == v' || not (freeInTk' f v tk || freeInKind' f v kd))

--freeInTk' :: (Var -> tm -> Bool) -> Var -> PrimTk tm -> Bool
freeInTk' f v (Tkt tp) = freeInType' f v tp
freeInTk' f v (Tkk kd) = freeInKind' f v kd
