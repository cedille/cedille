module Ctxt where
import Types


freshVars = ['a'..'z']
freshVarsNum = length freshVars

-- Evaluate "truncate (realToFrac (log 1000) / realToFrac (log 10))" to see why this is necessary
mylog base a
  | a >= base = succ (mylog base (a `div` base))
  | otherwise = 0

calcVar i = h "" (mylog freshVarsNum i) i where
  h v 0 i = reverse (freshVars !! i : v)
  h v place i =
    h (freshVars !! (i `div` freshVarsNum ^ place) : v) (pred place) (i - (i `div` freshVarsNum ^ place) * freshVarsNum ^ place)

-- Ordered Assoc List
type Oal a b = [(a, b)]

oalMod :: Ord a => Oal a b -> a -> (Maybe b -> b) -> Oal a b
oalMod ((ca, cb) : cs) a b =
  case compare a ca of
    GT -> (ca, cb) : oalMod cs a b
    LT -> (a, b Nothing) : (ca, cb) : cs
    EQ -> (a, b (Just cb)) : cs
oalMod [] a b = [(a, b Nothing)]

oalLookup :: Ord a => Oal a b -> a -> Maybe b
oalLookup ((ca, cb) : cs) a =
  case compare a ca of
    GT -> oalLookup cs a
    EQ -> Just cb
    LT -> Nothing
oalLookup [] _ = Nothing


data Trie a = Trie (Maybe a) (Oal Char (Trie a))

emptyTrie = Trie Nothing []

trieSingle "" v = Trie (Just v) []
trieSingle (c : cs) v = Trie Nothing [(c, trieSingle cs v)]

trieInsert' (Trie a os) (c : cs) v =
  Trie a $ oalMod os c $ maybe (maybe emptyTrie (trieSingle cs) v) $ \ t -> trieInsert' t cs v
trieInsert' (Trie _ os) "" v = Trie v os

trieInsert t k = trieInsert' t k . Just
trieRemove t k = trieInsert' t k Nothing

trieAt (Trie a os) (c : cs) = oalLookup os c >>= \ t -> trieAt t cs
trieAt t "" = Just t

trieLookup t k = trieAt t k >>= \ (Trie v _) -> v

trieMember t k = maybe False (\ _ -> True) $ trieLookup t k

trieMappings t = reverse $ h t "" [] where
  h (Trie a os) pfx acc = foldr (\ (c, t) ms -> h t (c : pfx) ms) (maybe acc (\ a -> (reverse pfx, a) : acc) a) os

trieAdd t1 = foldr (\ (k, v) t -> trieInsert t k v) t1 . trieMappings

type VarMap = Trie Var
type Stringset = Trie ()
type TermDef = (Maybe PureTerm, Maybe PureType)
type TypeDef = (Maybe PureType, Maybe PureKind)
type ExternalDef = Either TermDef TypeDef
type InternalDef = Either PureTerm PureType
type ExternalDefs = Trie ExternalDef
type InternalDefs = Trie InternalDef
data Ctxt = Ctxt ExternalDefs InternalDefs VarMap Stringset Stringset

  
--varMapRep :: Trie String -> String -> String
varMapRep m k = maybe k id $ trieLookup m k

ctxtClearExternals (Ctxt es is vs rs as) = Ctxt emptyTrie is vs rs as
ctxtClearSubst (Ctxt es is _ rs as) = Ctxt es is emptyTrie rs as
ctxtOnlySubst (Ctxt es is vs rs as) = Ctxt emptyTrie emptyTrie vs rs as
ctxtOnlyRename (Ctxt es is vs rs as) = Ctxt emptyTrie emptyTrie emptyTrie emptyTrie as
ctxtShowAll (Ctxt es is vs _ as) rs = Ctxt es is vs rs as
ctxtShown (Ctxt es is vs rs as) = rs

--emptyCtxt :: Ctxt
emptyCtxt = Ctxt emptyTrie emptyTrie emptyTrie emptyTrie emptyTrie

--ctxtLookup :: Ctxt -> Var -> Maybe ExternalDef
ctxtLookup (Ctxt es is vs rs as) v =
  let v' = varMapRep vs v in
  maybe
    (trieLookup es v' >>= Just . either
      (\ (tm, tp) -> Left (tm, trieLookup rs v' >> tp))
      (\ (tp, kd) -> Right (tp, trieLookup rs v' >> kd)))
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
ctxtLookupInternalTerm (Ctxt es is vs rs as) v = case trieLookup is (varMapRep vs v) of
  Just (Left tm) -> Just tm
  _ -> Nothing
  
--ctxtLookupInternalType :: Ctxt -> Var -> Maybe PureType
ctxtLookupInternalType (Ctxt es is vs rs as) v = case trieLookup is (varMapRep vs v) of
  Just (Right tp) -> Just tp
  _ -> Nothing
  
--ctxtDef :: Ctxt -> Var -> ExternalDef -> Ctxt
ctxtDef c "_" d = c
ctxtDef (Ctxt es is vs rs as) v d = Ctxt (trieInsert es v d) is (trieRemove vs v) (trieInsert rs v ()) (trieInsert as v ())

--ctxtInternalDef :: Ctxt -> Var -> InternalDef -> Ctxt
ctxtInternalDef c "_" d = c
ctxtInternalDef (Ctxt es is vs rs as) v d = Ctxt es (trieInsert is v d) (trieRemove vs v) (trieInsert rs v ()) (trieInsert as v ())

--ctxtDefTerm :: Ctxt -> Var -> TermDef -> Ctxt
ctxtDefTerm c v = ctxtDef c v . Left

--ctxtDefType :: Ctxt -> Var -> TypeDef -> Ctxt
ctxtDefType c v = ctxtDef c v . Right

ctxtDefTpKd c v (TpKdTp tp) = ctxtDefTerm c v (Nothing, Just tp)
ctxtDefTpKd c v (TpKdKd kd) = ctxtDefType c v (Nothing, Just kd)

--ctxtRename :: Ctxt -> Var -> Var -> Ctxt
ctxtRename c "_" _ = c
ctxtRename c _ "_" = c
ctxtRename (Ctxt es is vs rs as) v v' =
  let v'' = varMapRep vs v' in
  Ctxt es is (if v == v'' then trieRemove vs v else trieInsert vs v v'') rs {-(trieInsert rs v'' ())-} (trieInsert (trieInsert as v ()) v'' ())

--ctxtRep :: Ctxt -> Var -> Var
ctxtRep (Ctxt es is vs rs as) = varMapRep vs

--ctxtBindsVar :: Ctxt -> Var -> Bool
ctxtBindsVar (Ctxt es is vs rs as) v = trieMember as v

freshVar c "_" = "_"
freshVar (Ctxt _ _ _ _ as) v = maybe v (\ t -> v ++ h t 0) (trieAt as v) where
  h t i = let v = calcVar i in if trieMember t v then h t (succ i) else v

freshVar2 c "_" "_" = "_"
freshVar2 c "_" v = freshVar2 c v v
freshVar2 c v "_" = freshVar2 c v v
freshVar2 (Ctxt _ _ _ _ as, Ctxt _ _ _ _ as') v _ = h (maybe emptyTrie id $ trieAt as v) (maybe emptyTrie id $ trieAt as' v) 0 where
  h t t' i = let v = calcVar i in if trieMember t v || trieMember t' v then h t t' (succ i) else v
