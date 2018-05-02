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
eraseTerm (TmIota tm1 tm2 v tp) = eraseTerm tm1
eraseTerm (IotaProj1 tm) = eraseTerm tm
eraseTerm (IotaProj2 tm) = eraseTerm tm
eraseTerm (Beta pt pt') = pt'
eraseTerm (Sigma tm) = eraseTerm tm
eraseTerm (Delta tp tm) = eraseTerm tm
eraseTerm (Rho tm v tp tm') = eraseTerm tm'
eraseTerm (Phi tm tm' pt) = pt

--eraseType :: Type -> PureType
eraseType (TpVar v) = TpVar v
eraseType (TpLambda v tk tp) = TpLambda v (eraseTpKd tk) (eraseType tp)
eraseType (TpAll v tk tp) = TpAll v (eraseTpKd tk) (eraseType tp)
eraseType (TpPi v tp tp') = TpPi v (eraseType tp) (eraseType tp')
eraseType (TpEq ptm ptm') = TpEq ptm ptm'
eraseType (TpAppTp tp tp') = TpAppTp (eraseType tp) (eraseType tp')
eraseType (TpAppTm tp tm) = TpAppTm (eraseType tp) (eraseTerm tm)
eraseType (TpIota v tp tp') = TpIota v (eraseType tp) (eraseType tp')

--eraseKind :: Kind -> PureKind
eraseKind Star = Star
eraseKind (KdPi v tk kd) = KdPi v (eraseTpKd tk) (eraseKind kd)

--eraseTpKd :: TpKd -> PureTpKd
eraseTpKd (TpKdt tp) = TpKdt (eraseType tp)
eraseTpKd (TpKdk kd) = TpKdk (eraseKind kd)


substTerm = hnfTerm . ctxtClearExternals
substType = hnfType . ctxtClearExternals
substKind = hnfKind . ctxtClearExternals
substTpKd   = hnfTpKd   . ctxtClearExternals

--hnfTerm :: Ctxt -> PureTerm -> PureTerm
hnfTerm c (PureVar v) = maybe (PureVar (ctxtRep c v)) id (ctxtLookupTermVar c v)
hnfTerm c (PureApp tm tm') = case hnfTerm c tm of
  PureLambda v tm'' -> hnfTerm (ctxtInternalDef c v (Left (hnfTerm (ctxtRename c v v) tm'))) tm''
  tm'' -> PureApp tm'' (substTerm c tm')
hnfTerm c (PureLambda v tm) = doRename' c v $ \ v' ->
  let c' = ctxtRename c v v' in
  let tm' = hnfTerm c' tm in
  let etm = PureLambda v' tm' in case tm' of
    (PureApp htm atm) -> case hnfTerm c' atm of
      (PureVar v'') -> if v' == v'' && not (freeInTerm v' htm) then htm else etm
      _ -> etm
    _ -> etm

tkIsType (TpKdt _) = True
tkIsType (TpKdk _) = False
  
--hnfType :: Ctxt -> PureType -> PureType
hnfType c (TpVar v) = maybe (TpVar (ctxtRep c v)) id (ctxtLookupTypeVar c v)
hnfType c (TpLambda v tk tp) = doRename' c v $ \ v' ->
  let c' = ctxtRename c v v' in
  let tp' = hnfType c' tp in
  let tk' = substTpKd c tk in
  let etp = TpLambda v' tk' tp' in case tp' of
    (TpAppTp htp atp) -> case hnfType c' atp of
      (TpVar v'') -> if not (tkIsType tk) && v' == v'' && not (freeInType v' htp) then htp else etp
      _ -> etp
    (TpAppTm htp tm) -> case hnfTerm c' tm of
      (PureVar v'') -> if tkIsType tk && v' == v'' && not (freeInType v' htp) then htp else etp
      _ -> etp
    _ -> etp
hnfType c (TpAll v tk tp) =
  doRename' c v $ \ v' -> TpAll v' (substTpKd c tk) (hnfType (ctxtRename c v v') tp)
hnfType c (TpPi v tp tp') =
  doRename' c v $ \ v' -> TpPi v' (substType c tp) (hnfType (ctxtRename c v v') tp')
hnfType c (TpIota v tp tp') =
  doRename' c v $ \ v' -> TpIota v' (substType c tp) (substType (ctxtRename c v v') tp')
hnfType c (TpAppTp tp tp') = case hnfType c tp of
  TpLambda v (TpKdk _) tp'' -> hnfType (ctxtInternalDef c v (Right (hnfType (ctxtRename c v v) tp'))) tp''
  tp'' -> TpAppTp tp'' (substType c tp')
hnfType c (TpAppTm tp tm) = case hnfType c tp of
  TpLambda v (TpKdt _) tp' -> hnfType (ctxtInternalDef c v (Left (hnfTerm (ctxtRename c v v) tm))) tp'
  tp' -> TpAppTm tp' (substTerm c tm)
hnfType c (TpEq tm tm') = TpEq (substTerm c tm) (substTerm c tm')

--hnfKind :: Ctxt -> PureKind -> PureKind
hnfKind c Star = Star
hnfKind c (KdPi v tk kd) =
  doRename' c v $ \ v' -> KdPi v' (substTpKd c tk) (hnfKind (ctxtRename c v v') kd)

--hnfTpKd :: Ctxt -> PureTpKd -> PureTpKd
hnfTpKd c (TpKdt tp) = TpKdt (hnfType c tp)
hnfTpKd c (TpKdk kd) = TpKdk (hnfKind c kd)

hnfeTerm c = hnfTerm c . eraseTerm
hnfeType c = hnfType c . eraseType
hnfeKind c = hnfKind c . eraseKind
hnfeTpKd c = hnfTpKd c . eraseTpKd

convTerm c tm tm' = convTerm' c (hnfTerm c tm) (hnfTerm c tm')
convType c tp tp' = convType' c (hnfType c tp) (hnfType c tp')
convKind c kd kd' = convKind' c (hnfKind c kd) (hnfKind c kd')
convTpKd c tk tk' = convTpKd' c (hnfTpKd c tk) (hnfTpKd c tk')

--convTerm' :: Ctxt -> PureTerm -> PureTerm -> Bool
convTerm' c (PureVar v) (PureVar v') =
  ctxtRep c v == ctxtRep c v'
convTerm' c (PureLambda v tm) (PureLambda v' tm') = convTerm' (ctxtRename c v v') tm tm'
convTerm' c (PureApp tm tm') (PureApp tm'' tm''') = convTerm' c tm tm'' && convTerm c tm' tm'''
convTerm' _ _ _ = False

--convType' :: Ctxt -> PureType -> PureType -> Bool
convType' c (TpVar v) (TpVar v') = ctxtRep c v == ctxtRep c v'
convType' c (TpLambda v tk tp) (TpLambda v' tk' tp') = convTpKd c tk tk' && convType' (ctxtRename c v v') tp tp'
convType' c (TpAll v tk tp) (TpAll v' tk' tp') = convTpKd c tk tk' && convType' (ctxtRename c v v') tp tp'
convType' c (TpPi v tp tp') (TpPi v' tp'' tp''') = convType c tp tp'' && convType' (ctxtRename c v v') tp' tp'''
convType' c (TpIota v tp tp') (TpIota v' tp'' tp''') = convType c tp tp'' && convType (ctxtRename c v v') tp' tp'''
convType' c (TpEq tm tm') (TpEq tm'' tm''') = convTerm c tm tm'' && convTerm c tm' tm'''
convType' c (TpAppTp tp tp') (TpAppTp tp'' tp''') = convType' c tp tp'' && convType c tp' tp'''
convType' c (TpAppTm tp tm) (TpAppTm tp' tm') = convType' c tp tp' && convTerm c tm tm'
convType' _ _ _ = False

--convKind' :: Ctxt -> PureKind -> PureKind -> Bool
convKind' c Star Star = True
convKind' c (KdPi v tk kd) (KdPi v' tk' kd') = convTpKd c tk tk' && convKind' (ctxtRename c v v') kd kd'
convKind' _ _ _ = False

convTpKd' c (TpKdt tp) (TpKdt tp') = convType' c tp tp'
convTpKd' c (TpKdk kd) (TpKdk kd') = convKind' c kd kd'
convTpKd' _ _ _ = False

--freeInTerm :: Var -> PureTerm -> Bool
freeInTerm v (PureVar v') = v == v'
freeInTerm v (PureApp tm tm') = freeInTerm v tm || freeInTerm v tm'
freeInTerm v (PureLambda v' tm) = not (v == v') && freeInTerm v tm

--freeInType :: Var -> PureType -> Bool
freeInType v (TpVar v') = v == v'
freeInType v (TpLambda v' tk tp) = not (v == v') && (freeInTpKd v tk || freeInType v tp)
freeInType v (TpAll v' tk tp) = not (v == v') && (freeInTpKd v tk || freeInType v tp)
freeInType v (TpPi v' tp tp') = not (v == v') && (freeInType v tp || freeInType v tp')
freeInType v (TpIota v' tp tp') = not (v == v') && (freeInType v tp || freeInType v tp')
freeInType v (TpEq tm tm') = freeInTerm v tm || freeInTerm v tm'
freeInType v (TpAppTp tp tp') = freeInType v tp || freeInType v tp'
freeInType v (TpAppTm tp tm) = freeInType v tp || freeInTerm v tm

--freeInKind :: Var -> PureKind -> Bool
freeInKind v Star = False
freeInKind v (KdPi v' tk kd) = not (v == v') && (freeInTpKd v tk || freeInKind v kd)

--freeInTpKd :: Var -> PureTpKd -> Bool
freeInTpKd v (TpKdt tp) = freeInType v tp
freeInTpKd v (TpKdk kd) = freeInKind v kd
