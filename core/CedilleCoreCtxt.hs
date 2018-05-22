module CedilleCoreCtxt where
import CedilleCoreTypes

type Cal a = [(Char, a)]

calLookup [] c = Nothing
calLookup ((c', a) : l) c
  | c == c' = Just a
  | otherwise = calLookup l c

calInsert [] c a = (c, a) : []
calInsert ((c', a') : l) c a
  | c == c' = (c, a) : l
  | otherwise = (c', a') : calInsert l c a

data Trie a = Node (Maybe a) (Cal (Trie a))

emptyTrie = Node Nothing []

trieLookup (Node a ts) (c : cs) = calLookup ts c >>= \ t -> trieLookup t cs
trieLookup (Node a ts) [] = a

trieInsert (Node a ts) (c : cs) a' = maybe
  (Node a ((c, trieInsert emptyTrie cs a') : ts))
  (\ t -> Node a (calInsert ts c (trieInsert t cs a')))
  (calLookup ts c)
trieInsert (Node a ts) [] a' = Node (Just a') ts

trieMember t s = maybe False (\ _ -> True) (trieLookup t s)

trieAt t "" = t
trieAt (Node a ts) (c : cs) = maybe emptyTrie (\ t -> trieAt t cs) (calLookup ts c)


type VarMap = Trie Var
type VarMapRange = Trie ()
type TermDef = (Maybe PureTerm, Maybe PureType)
type TypeDef = (Maybe PureType, Maybe PureKind)
type ExternalDef = Either TermDef TypeDef
type InternalDef = Either PureTerm PureType
type ExternalDefs = Trie ExternalDef
type InternalDefs = Trie InternalDef
data Ctxt = Ctxt ExternalDefs InternalDefs VarMap VarMapRange

--varMapRep :: Trie a -> a -> a
varMapRep m k = case trieLookup m k of
  Just v -> v
  Nothing -> k

ctxtClearExternals (Ctxt es is vs rs) = Ctxt emptyTrie is vs rs

--emptyCtxt :: Ctxt
emptyCtxt = Ctxt emptyTrie emptyTrie emptyTrie emptyTrie

--ctxtLookup :: Ctxt -> Var -> Maybe ExternalDef
ctxtLookup (Ctxt es is vs rs) v = let v' = varMapRep vs v in
  maybe
    (trieLookup es v')
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
ctxtLookupInternalTerm (Ctxt es is vs rs) v = case trieLookup is (varMapRep vs v) of
  Just (Left tm) -> Just tm
  _ -> Nothing
  
--ctxtLookupInternalType :: Ctxt -> Var -> Maybe PureType
ctxtLookupInternalType (Ctxt es is vs rs) v = case trieLookup is (varMapRep vs v) of
  Just (Right tp) -> Just tp
  _ -> Nothing
  
--ctxtDef :: Ctxt -> Var -> ExternalDef -> Ctxt
ctxtDef c "_" d = c
ctxtDef (Ctxt es is vs rs) v d = Ctxt (trieInsert es v d) is (trieInsert vs v v) rs

--ctxtInternalDef :: Ctxt -> Var -> InternalDef -> Ctxt
ctxtInternalDef c "_" d = c
ctxtInternalDef (Ctxt es is vs rs) v d = Ctxt es (trieInsert is v d) (trieInsert vs v v) rs

--ctxtDefTerm :: Ctxt -> Var -> TermDef -> Ctxt
ctxtDefTerm c v d = ctxtDef c v (Left d)

--ctxtDefType :: Ctxt -> Var -> TypeDef -> Ctxt
ctxtDefType c v d = ctxtDef c v (Right d)

ctxtDefTpKd c v (TpKdTp tp) = ctxtDefTerm c v (Nothing, Just tp)
ctxtDefTpKd c v (TpKdKd kd) = ctxtDefType c v (Nothing, Just kd)

--ctxtRename :: Ctxt -> Var -> Var -> Ctxt
ctxtRename c "_" _ = c
ctxtRename c _ "_" = c
ctxtRename (Ctxt es is vs rs) v v' =
  let v'' = varMapRep vs v' in
  Ctxt es is (trieInsert vs v v'') (trieInsert rs v'' ())

--ctxtRep :: Ctxt -> Var -> Var
ctxtRep (Ctxt es is vs rs) = varMapRep vs

--ctxtBindsVar :: Ctxt -> Var -> Bool
ctxtBindsVar (Ctxt es is vs rs) v = trieMember vs v

-- Returns a fresh variable (v with primes) if v is already defined in ctxt
--doRename :: Ctxt -> Var -> Maybe Var
doRename c @ (Ctxt es is vs rs) v
  | trieMember vs v || trieMember rs v =
    let v'= v ++ "'" in
    maybe (Just v') Just (doRename c v')
  | otherwise = Nothing

{-
doRename c "_" = Nothing
doRename (Ctxt es is vs) v = case trieAt vs v of
  (Node Nothing _) -> Nothing
  t -> Just (v ++ h t)
  where
    h (Node Nothing _) = ""
    h (Node (Just _) ts) = maybe "\'" (\ t -> '\'' : h t) (calLookup ts '\'')
-}
--doRename' :: Ctxt -> Var -> (Var -> a) -> a
doRename' c v f = maybe (f v) f (doRename c v)

