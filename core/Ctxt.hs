module Ctxt where
import Types
import qualified Data.Map.Lazy as Map

type Trie a = Map.Map String a
emptyTrie = Map.empty
trieInsert t k v = Map.insert k v t
trieLookup t k = Map.lookup k t
trieMember t k = Map.member k t
trieRemove t k = Map.delete k t
trieMappings = Map.assocs
trieAdd t1 t2 = Map.union t2 t1

type VarMap = Trie Var
type VarMapRange = Trie ()
type TermDef = (Maybe PureTerm, Maybe PureType)
type TypeDef = (Maybe PureType, Maybe PureKind)
type ExternalDef = Either TermDef TypeDef
type InternalDef = Either PureTerm PureType
type ExternalDefs = Trie ExternalDef
type InternalDefs = Trie InternalDef
data Ctxt = Ctxt ExternalDefs InternalDefs VarMap VarMapRange

  
--varMapRep :: Trie String -> String -> String
varMapRep m k = maybe k id $ trieLookup m k

ctxtClearExternals (Ctxt es is vs rs) = Ctxt emptyTrie is vs rs
ctxtClearSubst (Ctxt es is _ rs) = Ctxt es is emptyTrie rs
ctxtOnlySubst (Ctxt es is vs rs) = Ctxt emptyTrie emptyTrie vs rs
ctxtShowAll (Ctxt es is vs _) rs = Ctxt es is vs rs
ctxtShown (Ctxt es is vs rs) = rs

--emptyCtxt :: Ctxt
emptyCtxt = Ctxt emptyTrie emptyTrie emptyTrie emptyTrie

--ctxtLookup :: Ctxt -> Var -> Maybe ExternalDef
ctxtLookup (Ctxt es is vs rs) v =
  let v' = varMapRep vs v in
  maybe
    (trieLookup rs v' >> trieLookup es v')
    (\ d -> case d of
      (Left tmd) -> Just (Left (Just tmd, Nothing))
      (Right tpd) -> Just (Right (Just tpd, Nothing)))
    (trieLookup is v')

--ctxtLookupTerm :: Ctxt -> Var -> Maybe TermDef
ctxtLookupTerm c v = case ctxtLookup c v of
  Just (Left tmd) -> Just tmd
  _ -> Nothing

--ctxtLookupType :: Ctxt -> Var -> Maybe TypeDef
ctxtLookupType c v = case ctxtLookup c v of
  Just (Right tpd) -> Just tpd
  _ -> Nothing

--ctxtLookupTermVar :: Ctxt -> Var -> Maybe PureTerm
ctxtLookupTermVar c v = ctxtLookupTerm c v >>= fst
  
--ctxtLookupVarType :: Ctxt -> Var -> Maybe PureType
ctxtLookupVarType c v = ctxtLookupTerm c v >>= snd
  
--ctxtLookupTypeVar :: Ctxt -> Var -> Maybe PureType
ctxtLookupTypeVar c v = ctxtLookupType c v >>= fst

--ctxtLookupVarKind :: Ctxt -> Var -> Maybe PureKind
ctxtLookupVarKind c v = ctxtLookupType c v >>= snd

--ctxtLookupInternalTerm :: Ctxt -> Var -> Maybe PureTerm
ctxtLookupInternalTerm (Ctxt es is vs rs) v = case trieLookup is (varMapRep vs v) of
  Just (Left tm) -> Just tm
  _ -> Nothing
  
--ctxtLookupInternalType :: Ctxt -> Var -> Maybe PureType
ctxtLookupInternalType (Ctxt es is vs rs) v = case trieLookup is (varMapRep vs v) of
  Just (Right tp) -> Just tp
  _ -> Nothing
  
--ctxtDef :: Ctxt -> Var -> ExternalDef -> Ctxt
ctxtDef c "_" d = c
ctxtDef (Ctxt es is vs rs) v d = Ctxt (trieInsert es v d) is (trieRemove vs v) (trieInsert rs v ())

--ctxtInternalDef :: Ctxt -> Var -> InternalDef -> Ctxt
ctxtInternalDef c "_" d = c
ctxtInternalDef (Ctxt es is vs rs) v d = Ctxt es (trieInsert is v d) (trieRemove vs v) (trieInsert rs v ())

--ctxtDefTerm :: Ctxt -> Var -> TermDef -> Ctxt
ctxtDefTerm c v = ctxtDef c v . Left

--ctxtDefType :: Ctxt -> Var -> TypeDef -> Ctxt
ctxtDefType c v = ctxtDef c v . Right

ctxtDefTpKd c v (TpKdTp tp) = ctxtDefTerm c v (Nothing, Just tp)
ctxtDefTpKd c v (TpKdKd kd) = ctxtDefType c v (Nothing, Just kd)

--ctxtRename :: Ctxt -> Var -> Var -> Ctxt
ctxtRename c "_" _ = c
ctxtRename c _ "_" = c
ctxtRename (Ctxt es is vs rs) v v' =
  let v'' = varMapRep vs v' in
  Ctxt es is (if v == v'' then trieRemove vs v else trieInsert vs v v'') (trieInsert rs v'' ())

--ctxtRep :: Ctxt -> Var -> Var
ctxtRep (Ctxt es is vs rs) = varMapRep vs

--ctxtBindsVar :: Ctxt -> Var -> Bool
ctxtBindsVar (Ctxt es is vs rs) v = trieMember vs v || trieMember rs v

--freshVar :: Ctxt -> Var -> (Var -> a) -> a
freshVar c "_" f = f "_"
freshVar c@(Ctxt es is vs rs) v f =
  case Map.splitLookup v rs of
    (_, Just _, rs) -> freshVar (Ctxt es is vs rs) (v ++ "\'") f
    (_, Nothing, rs) -> case Map.splitLookup v vs of
      (_, Just _, vs) -> freshVar (Ctxt es is vs rs) (v ++ "\'") f
      (_, Nothing, vs) -> f v
    
--freshVar2 :: (Ctxt, Ctxt) -> Var -> Var -> (Var -> a) -> a
freshVar2 c "_" "_" f = f "_"
freshVar2 c "_" v f = freshVar2 c v v f
freshVar2 (Ctxt _ _ vs rs, Ctxt _ _ vs' rs') v _ f = f $ h vs vs' rs rs' v where
  prime v = v ++ "\'"
  h vs vs' rs rs' v =
    case Map.splitLookup v rs of
      (_, Just _, rs) -> h vs vs' rs rs' (prime v)
      (_, Nothing, rs) -> case Map.splitLookup v rs' of
        (_, Just _, rs') -> h vs vs' rs rs' (prime v)
        (_, Nothing, rs') -> case Map.splitLookup v vs of
          (_, Just _, vs) -> h vs vs' rs rs' (prime v)
          (_, Nothing, vs) -> case Map.splitLookup v vs' of
            (_, Just _, vs') -> h vs vs' rs rs' (prime v)
            (_, Nothing, vs') -> v
