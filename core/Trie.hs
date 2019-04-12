module Trie where

-- Ordered Assoc List
type Oal a b = [(a, b)]

--oalMod :: Ord a => Oal a b -> a -> (Maybe b -> b) -> Oal a b
oalMod ((ca, cb) : cs) a b =
  case compare a ca of
    GT -> (ca, cb) : oalMod cs a b
    LT -> (a, b Nothing) : (ca, cb) : cs
    EQ -> (a, b (Just cb)) : cs
oalMod [] a b = [(a, b Nothing)]

--oalLookup :: Ord a => Oal a b -> a -> Maybe b
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

trieInsert (Trie a os) (c : cs) v =
  Trie a $ oalMod os c $ maybe (trieSingle cs v) $ \ t -> trieInsert t cs v
trieInsert (Trie _ os) "" v = Trie (Just v) os

trieLookup (Trie a os) (c : cs) = oalLookup os c >>= \ t -> trieLookup t cs
trieLookup (Trie a os) "" = a

trieStrings t = h t "" [] where
  h (Trie a os) pfx acc = foldr
    (\ (c, t) ms -> h t (c : pfx) ms)
    (maybe acc (\ a -> reverse pfx : acc) a) os
