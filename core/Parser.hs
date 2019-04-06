module Parser where
import Types

data Token =
    TVar String
  | TLam       -- λ
  | TLamE      -- Λ
  | TPi        -- Π
  | TAll       -- ∀
  | TIota      -- ι
  | TBeta      -- β
  | TRho       -- ρ
  | TSigma     -- ς
  | TPhi       -- φ
  | TStar      -- ★
  | TAsyEq     -- ≃
  | TDelta     -- δ
  | TProj1     -- .1
  | TProj2     -- .2
  | TEq        -- =
  | TAt        -- @
  | TDot       -- .
  | TCenterDot -- ·
  | TDash      -- -
  | TColon     -- :
  | TComma     -- ,
  | TParenL    -- (
  | TParenR    -- )
  | TBracketL  -- [
  | TBracketR  -- ]
  | TBraceL    -- {
  | TBraceR    -- }
  | TAngleL    -- <
  | TAngleR    -- >
  deriving (Show, Eq)


isVarChar c =
  (c >= 'a' && c <= 'z') ||
  (c >= 'A' && c <= 'Z') ||
  (c >= '0' && c <= '9') ||
  (c == '-') ||
  (c == '\'') ||
  (c == '_')

lexProj ts (' ' : s) = lexProj ts s
lexProj ts ('\n' : s) = lexProj ts s
lexProj ts ('\t' : s) = lexProj ts s
lexProj ts ('1' : s) = lexStr (TProj1 : ts) s
lexProj ts ('2' : s) = lexStr (TProj2 : ts) s
lexProj ts s = lexStr (TDot : ts) s

--lexVar :: String -> String -> Maybe (String, String)
lexVar v (c : s)
  | isVarChar c = lexVar (c : v) s
  | foldr (\ c' x -> x || (c == c')) False " \n\tΠ∀λΛιβδςρφ≃★@=◂,.·:-()[]{}<>" = Just (reverse v, (c : s))
  | otherwise = Nothing
lexVar v "" = Just (reverse v, "")

--lexStr :: [Token] -> String -> Maybe [Token]
lexStr ts (' ' : s) = lexStr ts s
lexStr ts ('\n' : s) = lexStr ts s
lexStr ts ('\t' : s) = lexStr ts s
lexStr ts ('.' : s) = lexProj ts s
lexStr ts ('λ' : s) = lexStr (TLam : ts) s
lexStr ts ('Λ' : s) = lexStr (TLamE : ts) s
lexStr ts ('Π' : s) = lexStr (TPi : ts) s
lexStr ts ('∀' : s) = lexStr (TAll : ts) s
lexStr ts ('ι' : s) = lexStr (TIota : ts) s
lexStr ts ('β' : s) = lexStr (TBeta : ts) s
lexStr ts ('ρ' : s) = lexStr (TRho : ts) s
lexStr ts ('ς' : s) = lexStr (TSigma : ts) s
lexStr ts ('φ' : s) = lexStr (TPhi : ts) s
lexStr ts ('δ' : s) = lexStr (TDelta : ts) s
lexStr ts ('★' : s) = lexStr (TStar : ts) s
lexStr ts ('≃' : s) = lexStr (TAsyEq : ts) s
lexStr ts ('=' : s) = lexStr (TEq : ts) s
lexStr ts ('@' : s) = lexStr (TAt : ts) s
lexStr ts (':' : s) = lexStr (TColon : ts) s
lexStr ts ('·' : s) = lexStr (TCenterDot : ts) s
lexStr ts ('-' : '-' : s) = lexComment ts Nothing s
lexStr ts ('{' : '-' : s) = lexComment ts (Just 0) s
lexStr ts ('-' : s) = lexStr (TDash : ts) s
lexStr ts (',' : s) = lexStr (TComma : ts) s
lexStr ts ('(' : s) = lexStr (TParenL : ts) s
lexStr ts (')' : s) = lexStr (TParenR : ts) s
lexStr ts ('[' : s) = lexStr (TBracketL : ts) s
lexStr ts (']' : s) = lexStr (TBracketR : ts) s
lexStr ts ('{' : s) = lexStr (TBraceL : ts) s
lexStr ts ('}' : s) = lexStr (TBraceR : ts) s
lexStr ts ('<' : s) = lexStr (TAngleL : ts) s
lexStr ts ('>' : s) = lexStr (TAngleR : ts) s
lexStr ts (c : s) = if isVarChar c
  then lexVar (c : "") s >>= uncurry (\ v -> lexStr (TVar v : ts))
  else Nothing
lexStr ts "" = Just $ reverse ts

-- Nothing => single-line comment; Just x => x nested multi-line comments
lexComment ts Nothing ('\n' : s) = lexStr ts s
lexComment ts (Just 0) ('-' : '}' : s) = lexStr ts s
lexComment ts (Just x) ('-' : '}' : s) = lexComment ts (Just (pred x)) s
lexComment ts (Just x) ('{' : '-' : s) = lexComment ts (Just (succ x)) s
lexComment ts multi (_ : s) = lexComment ts multi s
lexComment ts multi [] = Just $ reverse ts


newtype ParseM a = ParseM ([String] -> [Token] -> Maybe (a, [Token]))

parseMf (ParseM f) = f
parseMt xs ts (ParseM f) = f xs ts
parseMr = curry Just

parseDrop t = ParseM $ \ xs ts -> case ts of
  (t' : ts') -> if t == t' then parseMr () ts' else Nothing
  _ -> Nothing

parseLookup x = h 0 where
  h acc [] = Left x
  h acc (y : ys)
    | x == y = Right acc
    | True   = h (succ acc) ys

parseBind x (ParseM f) = ParseM $ \ xs ts -> f (x : xs) ts


instance Functor ParseM where
  fmap f (ParseM g) = ParseM $ \ xs ts -> g xs ts >>= \ p -> Just (f (fst p), snd p)

instance Applicative ParseM where
  pure = ParseM . const . parseMr
  ParseM f <*> ParseM g =
    ParseM $ \ xs ts -> f xs ts >>= \ p ->
    g xs (snd p) >>= \ p' ->
    Just (fst p (fst p'), snd p')

instance Monad ParseM where
  (ParseM f) >>= g = ParseM $ \ xs ts -> f xs ts >>= \ (a, ts') -> parseMf (g a) xs ts'


parseVar = ParseM $ \ xs ts -> case ts of
  (TVar v : ts) -> parseMr v ts
  _ -> Nothing

parsePrTermApp tm = ParseM $ \ xs ts -> maybe
  (parseMr tm ts)
  (\ (tm', ts') -> parseMt xs ts' $ parsePrTermApp (PrApp tm tm'))
  (parseMt xs ts parsePrTerm2)

parseTermApp tm = ParseM $ \ xs ts -> case ts of
  (TDash : ts) -> maybe
    (parseMr tm ts)
    (\ p -> parseMt xs (snd p) $ parseTermApp (TmAppTmE tm (fst p)))
    (parseMt xs ts parseTerm3)
  (TCenterDot : ts) -> maybe
    (parseMr tm ts)
    (\ p -> parseMt xs (snd p) $ parseTermApp (TmAppTp tm (fst p)))
    (parseMt xs ts $ parseType2 parseTerm3)
  _ -> maybe
    (parseMr tm ts)
    (\ p -> parseMt xs (snd p) $ parseTermApp (TmAppTm tm (fst p)))
    (parseMt xs ts parseTerm3)

parseTypeApp tm tp = ParseM $ \ xs ts -> case ts of
  (TCenterDot : ts) -> maybe
    (parseMr tp ts)
    (\ p -> parseMt xs (snd p) $ parseTypeApp tm (TpAppTp tp (fst p)))
    (parseMt xs ts $ parseType2 tm)
  _ -> maybe
    (parseMr tp ts)
    (\ p -> parseMt xs (snd p) $ parseTypeApp tm (TpAppTm tp (fst p)))
    (parseMt xs ts tm)

parseIotaProj tm = ParseM $ \ xs ts -> case ts of
  (TProj1 : ts) -> parseMt xs ts $ parseIotaProj (TmProj1 tm)
  (TProj2 : ts) -> parseMt xs ts $ parseIotaProj (TmProj2 tm)
  _ -> parseMr tm ts

parsePrTerm = ParseM $ \ xs ts -> case ts of
  (TLam : TVar v : ts) -> parseMt xs ts $ pure PrLam <* parseDrop TDot <*> parseBind v parsePrTerm
  _ -> parseMt xs ts parsePrTerm1
parsePrTerm1 = ParseM $ \ xs ts -> parseMt xs ts parsePrTerm2 >>= \ (t', ts') -> parseMf (parsePrTermApp t') xs ts'
parsePrTerm2 = ParseM $ \ xs ts -> case ts of
  (TVar v : ts) -> parseMr (either PrRef PrVar $ parseLookup v xs) ts
  (TParenL : ts) -> parseMt xs ts $ parsePrTerm <* parseDrop TParenR
  _ -> Nothing

parseTerm = ParseM $ \ xs ts -> case ts of
  (TLam : TVar v : ts) -> parseMt xs ts $ pure TmLam <* parseDrop TColon <*> parseType parseTerm3 <* parseDrop TDot <*> parseBind v parseTerm
  (TLamE : TVar v : ts) -> parseMt xs ts $ pure TmLamE <* parseDrop TColon <*> parseTpKd parseTerm3 <* parseDrop TDot <*> parseBind v parseTerm
  (TRho : ts) -> parseMt xs ts $ pure TmRho <*> parseTerm2 <* parseDrop TAt <*> (parseVar >>= \ v -> parseDrop TDot *> parseBind v (parseType parsePrTerm2)) <* parseDrop TDash <*> parseTerm
  (TPhi : ts) -> parseMt xs ts $ pure TmPhi <*> parseTerm2 <* parseDrop TDash <*> parseTerm <* parseDrop TBraceL <*> parsePrTerm <* parseDrop TBraceR
  (TDelta : ts) -> parseMt xs ts $ pure TmDelta <*> parseType2 parsePrTerm2 <* parseDrop TDash <*> parseTerm
  (TBracketL : TVar v : TEq : ts) -> parseMt xs ts $ pure TmLetTm <*> parseTerm <* parseDrop TBracketR <* parseDrop TDash <*> parseBind v parseTerm
  (TBraceL : TVar v : TEq : ts) -> parseMt xs ts $ pure TmLetTmE <*> parseTerm <* parseDrop TBraceR <* parseDrop TDash <*> parseBind v parseTerm
  (TBracketL : TVar v : TColon : ts) -> parseMt xs ts $ pure TmLetTp <*> parseKind parseTerm3 <* parseDrop TEq <*> parseType parseTerm3 <* parseDrop TBracketR <* parseDrop TDash <*> parseBind v parseTerm
  _ -> parseMt xs ts parseTerm1
parseTerm1 = ParseM $ \ xs ts -> parseMt xs ts parseTerm2 >>= \ (t, ts') -> parseMf (parseTermApp t) xs ts'
parseTerm2 = ParseM $ \ xs ts -> case ts of
  (TSigma : ts) -> parseMt xs ts $ pure TmSigma <*> parseTerm2
  _ -> parseMt xs ts parseTerm3
parseTerm3 = ParseM $ \ xs ts -> parseMt xs ts parseTerm4 >>= \ (t, ts') -> parseMf (parseIotaProj t) xs ts'
parseTerm4 = ParseM $ \ xs ts -> case ts of
  (TVar v : ts) -> parseMr (either TmRef TmVar $ parseLookup v xs) ts
  (TBeta : ts) -> parseMt xs ts $ pure TmBeta <* parseDrop TAngleL <*> parsePrTerm <* parseDrop TAngleR <* parseDrop TBraceL <*> parsePrTerm <* parseDrop TBraceR
  (TParenL : ts) -> parseMt xs ts $ parseTerm <* parseDrop TParenR
  (TBracketL : ts) -> parseMt xs ts $ pure TmIota <*> parseTerm <* parseDrop TComma <*> parseTerm <* parseDrop TAt <*> (parseVar >>= \ v -> parseDrop TDot *> parseBind v (parseType parseTerm3) <* parseDrop TBracketR)
  _ -> Nothing

parseType tm = ParseM $ \ xs ts -> case ts of
  (TLam : TVar v : ts) -> parseMt xs ts $ pure TpLam <* parseDrop TColon <*> parseTpKd tm <* parseDrop TDot <*> parseBind v (parseType tm)
  (TAll : TVar v : ts) -> parseMt xs ts $ pure TpAll <* parseDrop TColon <*> parseTpKd tm <* parseDrop TDot <*> parseBind v (parseType tm)
  (TPi : TVar v : ts) -> parseMt xs ts $ pure TpPi <* parseDrop TColon <*> parseType tm <* parseDrop TDot <*> parseBind v (parseType tm)
  (TIota : TVar v : ts) -> parseMt xs ts $ pure TpIota <* parseDrop TColon <*> parseType tm <* parseDrop TDot <*> parseBind v (parseType tm)
  _ -> parseMt xs ts $ parseType1 tm
parseType1 tm = ParseM $ \ xs ts -> parseMt xs ts (parseType2 tm) >>= \ (t, ts') -> parseMf (parseTypeApp tm t) xs ts'
parseType2 tm = ParseM $ \ xs ts -> case ts of
  (TVar v : ts) -> parseMr (either TpRef TpVar $ parseLookup v xs) ts
  (TBraceL : ts) -> parseMt xs ts $ pure TpEq <*> parsePrTerm <* parseDrop TAsyEq <*> parsePrTerm <* parseDrop TBraceR
  (TParenL : ts) -> parseMt xs ts $ parseType tm <* parseDrop TParenR
  _ -> Nothing

parseKind tm = ParseM $ \ xs ts -> case ts of
  (TStar : ts) -> parseMr KdStar ts
  (TPi : TVar v : ts) -> parseMt xs ts $ pure KdPi <* parseDrop TColon <*> parseTpKd tm <* parseDrop TDot <*> parseBind v (parseKind tm)
  (TParenL : ts) -> parseMt xs ts $ parseKind tm <* parseDrop TParenR

parseTpKd tm = ParseM $ \ xs ts -> maybe (parseMf (fmap Right $ parseKind tm) xs ts) Just (parseMf (fmap Left $ parseType tm) xs ts)

parseCmd = ParseM $ \ xs ts -> case ts of
  (TVar "import" : ts) -> parseMt xs ts $ pure ImportCmd <*> parseVar <* parseDrop TDot
  (TVar v : TEq : ts) -> parseMt xs ts $ pure (TermCmd v) <*> parseTerm <* parseDrop TDot
  (TVar v : TColon : ts) -> parseMt xs ts $ pure (TypeCmd v) <*> parseKind parseTerm3 <* parseDrop TEq <*> parseType parseTerm3 <* parseDrop TDot
  _ -> Nothing
parseCmds = ParseM $ \ xs ts -> case ts of
  [] -> parseMr [] []
  _ -> parseMt xs ts $ pure (:) <*> parseCmd <*> parseCmds

parseDropModuleHeader = ParseM $ \ xs ts -> case ts of
  (TVar "module" : TVar mn : TDot : ts) -> parseMr () ts
  _ -> parseMr () ts

parseStr (ParseM f) s = lexStr [] s >>= f []

parseFile = parseStr (parseDropModuleHeader *> parseCmds)
