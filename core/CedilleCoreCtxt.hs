module CedilleCoreCtxt where
import qualified Data.Map as Map
import CedilleCoreTypes

type VarMap = Map.Map Var Var
type TermDef = (Maybe PureTerm, Maybe PureType)
type TypeDef = (Maybe PureType, Maybe PureKind)
type ExternalDef = Either TermDef TypeDef
type InternalDef = Either PureTerm PureType
type ExternalDefs = Map.Map Var ExternalDef
type InternalDefs = Map.Map Var InternalDef
data Ctxt = Ctxt ExternalDefs InternalDefs VarMap

maybeOr Nothing m = m
maybeOr m m' = m

mapsLookup k m m' = maybeOr (Map.lookup k m) (Map.lookup k m')

--varMapRep :: Ord a => Map.Map a a -> a -> a
varMapRep m k = case Map.lookup k m of
  Just v -> v
  Nothing -> k

--varMapRep' :: VarMap -> Var -> (Var -> a) -> a
varMapRep' vs v f = f (varMapRep vs v)

ctxtVarMap (Ctxt es is vs) = vs
ctxtExternals (Ctxt es is vs) = es
ctxtInternals (Ctxt es is vs) = is
ctxtClearExternals (Ctxt es is vs) = Ctxt Map.empty is vs

--emptyCtxt :: Ctxt
emptyCtxt = Ctxt Map.empty Map.empty Map.empty

--ctxtLookup :: Ctxt -> Var -> Maybe ExternalDef
ctxtLookup (Ctxt es is vs) v = let v' = varMapRep vs v in
  maybe
    (Map.lookup v' es)
    (\ d -> case d of
        (Left tmd) -> Just (Left (Just tmd, Nothing))
        (Right tpd) -> Just (Right (Just tpd, Nothing)))
    (Map.lookup v' is)

--ctxtLookupTerm :: Ctxt -> Var -> Maybe TermDef
ctxtLookupTerm c v = case ctxtLookup c v of
  Just (Left tmd) -> Just tmd
  _ -> Nothing

--ctxtLookupType :: Ctxt -> Var -> Maybe TypeDef
ctxtLookupType c v = case ctxtLookup c v of
  Just (Right tpd) -> Just tpd
  _ -> Nothing

--ctxtLookupTermVar :: Ctxt -> Var -> Maybe PureTerm
ctxtLookupTermVar c v = case ctxtLookupTerm c v of
  Just (tm, tp) -> tm
  Nothing -> Nothing
  
--ctxtLookupVarType :: Ctxt -> Var -> Maybe PureType
ctxtLookupVarType c v = case ctxtLookupTerm c v of
  Just (tm, tp) -> tp
  Nothing -> Nothing
  
--ctxtLookupTypeVar :: Ctxt -> Var -> Maybe PureType
ctxtLookupTypeVar c v = case ctxtLookupType c v of
  Just (tp, kd) -> tp
  Nothing -> Nothing

--ctxtLookupVarKind :: Ctxt -> Var -> Maybe PureKind
ctxtLookupVarKind c v = case ctxtLookupType c v of
  Just (tp, kd) -> kd
  Nothing -> Nothing

--ctxtLookupInternalTerm :: Ctxt -> Var -> Maybe PureTerm
ctxtLookupInternalTerm (Ctxt es is vs) v = case Map.lookup (varMapRep vs v) is of
  Just (Left tm) -> Just tm
  _ -> Nothing
  
--ctxtLookupInternalType :: Ctxt -> Var -> Maybe PureType
ctxtLookupInternalType (Ctxt es is vs) v = case Map.lookup (varMapRep vs v) is of
  Just (Right tp) -> Just tp
  _ -> Nothing
  
--ctxtDef :: Ctxt -> Var -> ExternalDef -> Ctxt
ctxtDef (Ctxt es is vs) v d = Ctxt (Map.insert v d es) is (Map.insert v v vs)

--ctxtInternalDef :: Ctxt -> Var -> InternalDef -> Ctxt
ctxtInternalDef (Ctxt es is vs) v d = Ctxt es (Map.insert v d is) (Map.insert v v vs)

--ctxtDefTerm :: Ctxt -> Var -> TermDef -> Ctxt
ctxtDefTerm c v d = ctxtDef c v (Left d)

--ctxtDefType :: Ctxt -> Var -> TypeDef -> Ctxt
ctxtDefType c v d = ctxtDef c v (Right d)

ctxtDefTk c v (Tkt tp) = ctxtDefTerm c v (Nothing, Just tp)
ctxtDefTk c v (Tkk kd) = ctxtDefType c v (Nothing, Just kd)

--ctxtRename :: Ctxt -> Var -> Var -> Ctxt
ctxtRename (Ctxt es is vs) v v' = Ctxt es is (Map.insert v (varMapRep vs v') vs)

--ctxtDeclVar :: Ctxt -> Var -> Ctxt
ctxtDeclVar (Ctxt es is vs) v = Ctxt (Map.delete v es) (Map.delete v is) (Map.insert v v vs)

--ctxtRep :: Ctxt -> Var -> Var
ctxtRep (Ctxt es is vs) = varMapRep vs

--ctxtBindsVar :: Ctxt -> Var -> Bool
ctxtBindsVar (Ctxt es is vs) v = Map.member v vs

-- Returns a fresh variable (v with primes) if v is already defined in ctxt
--doRename :: Ctxt -> Var -> Maybe Var
doRename c @ (Ctxt es is vs) v
  | Map.member v vs =
    let v'= v ++ "'" in
    maybe (Just v') Just (doRename c v')
  | otherwise = Nothing

--doRename' :: Ctxt -> Var -> (Var -> a) -> a
doRename' c v f = maybe (f v) f (doRename c v)
