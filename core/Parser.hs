module Parser where
import Types
import ToString

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
  | TTriangle  -- ◂
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


--consIf :: a -> Maybe [a] -> Maybe [a]
consIf a (Just as) = Just (a : as)
consIf a Nothing = Nothing

lexProj (' ' : s) = lexProj s
lexProj ('\n' : s) = lexProj s
lexProj ('\t' : s) = lexProj s
lexProj ('1' : s) = consIf TProj1 $ lexStr s
lexProj ('2' : s) = consIf TProj2 $ lexStr s
lexProj s = consIf TDot $ lexStr s

--lexVar :: Var -> String -> Maybe (String, String)
lexVar v (c : s)
  | isVarChar c = lexVar (c : v) s
  | foldr (\ c' x -> x || (c == c')) False " \n\tΠ∀λΛιβδςρφ≃★@=◂,.·:-()[]{}<>" = Just (reverse v, (c : s))
  | otherwise = Nothing
lexVar v "" = Just (reverse v, "")
{-
--lexImport :: String -> Maybe [Token]
lexImport s = h Nothing Nothing s where
--h :: Maybe String -> Maybe String -> String -> Maybe [Token]
  h Nothing Nothing (' ' : s) = h Nothing Nothing s
  h Nothing Nothing ('\n' : s) = h Nothing Nothing s
  h Nothing Nothing ('\t' : s) = h Nothing Nothing s
  h Nothing Nothing (c : s) = h (Just (c : "")) Nothing s
  h (Just fp) Nothing ('.' : s) = h (Just fp) (Just ".") s
  h (Just fp) Nothing (c : s) = h (Just (c : fp)) Nothing s
  h (Just fp) (Just afp) (' ' : s) = h (Just fp) (Just (' ' : s)) s
  h (Just fp) (Just afp) ('\t' : s) = h (Just fp) (Just ('\t' : s)) s
  h (Just fp) (Just afp) ('\n' : s) = consIf (TImport (reverse fp)) $ lexStr s
  h (Just fp) (Just afp) s = h (Just (afp ++ fp)) Nothing s
  h (Just fp) (Just afp) "" = Just (TImport (reverse fp) : [])
  h _ _ "" = Nothing
-}
--lexStr :: String -> Maybe [Token]
lexStr (' ' : s) = lexStr s
lexStr ('\n' : s) = lexStr s
lexStr ('\t' : s) = lexStr s
lexStr ('.' : s) = lexProj s
lexStr ('λ' : s) = consIf TLam $ lexStr s
lexStr ('Λ' : s) = consIf TLamE $ lexStr s
lexStr ('Π' : s) = consIf TPi $ lexStr s
lexStr ('∀' : s) = consIf TAll $ lexStr s
lexStr ('ι' : s) = consIf TIota $ lexStr s
lexStr ('β' : s) = consIf TBeta $ lexStr s
lexStr ('ρ' : s) = consIf TRho $ lexStr s
lexStr ('ς' : s) = consIf TSigma $ lexStr s
lexStr ('φ' : s) = consIf TPhi $ lexStr s
lexStr ('δ' : s) = consIf TDelta $ lexStr s
lexStr ('★' : s) = consIf TStar $ lexStr s
lexStr ('≃' : s) = consIf TAsyEq $ lexStr s
lexStr ('=' : s) = consIf TEq $ lexStr s
lexStr ('@' : s) = consIf TAt $ lexStr s
lexStr (':' : s) = consIf TColon $ lexStr s
lexStr ('·' : s) = consIf TCenterDot $ lexStr s
lexStr ('-' : s) = consIf TDash $ lexStr s
lexStr (',' : s) = consIf TComma $ lexStr s
lexStr ('◂' : s) = consIf TTriangle $ lexStr s
lexStr ('(' : s) = consIf TParenL $ lexStr s
lexStr (')' : s) = consIf TParenR $ lexStr s
lexStr ('[' : s) = consIf TBracketL $ lexStr s
lexStr (']' : s) = consIf TBracketR $ lexStr s
lexStr ('{' : s) = consIf TBraceL $ lexStr s
lexStr ('}' : s) = consIf TBraceR $ lexStr s
lexStr ('<' : s) = consIf TAngleL $ lexStr s
lexStr ('>' : s) = consIf TAngleR $ lexStr s
--lexStr ('i' : 'm' : 'p' : 'o' : 'r' : 't' : ' ' : s) = lexImport s
lexStr (c : s) = if isVarChar c
  then lexVar (c : "") s >>= uncurry (\ v -> consIf (TVar v) . lexStr)
  else Nothing
lexStr "" = Just []


newtype ParseM a = ParseM ([Token] -> Maybe (a, [Token]))

parseMf (ParseM f) = f
parseMt ts (ParseM f) = f ts
parseMr = curry Just
parseMor (ParseM f) (ParseM g) = ParseM $ \ ts -> maybe (g ts) Just (f ts)

instance Functor ParseM where
  fmap f (ParseM g) = ParseM $ \ ts -> g ts >>= \ p -> Just (f (fst p), snd p)

instance Applicative ParseM where
  pure = ParseM . parseMr
  ParseM f <*> ParseM g =
    ParseM $ \ ts -> f ts >>= \ p ->
    g (snd p) >>= \ p' ->
    Just (fst p (fst p'), snd p')

parseDrop t = ParseM $ \ ts -> case ts of
  (t' : ts') -> if t == t' then parseMr () ts' else Nothing
  _ -> Nothing

parseVar = ParseM $ \ ts -> case ts of
  (TVar v : ts) -> parseMr v ts
  _ -> Nothing

parsePureTermApp tm = ParseM $ \ ts -> maybe
  (parseMr tm ts)
  (\ p -> parseMt (snd p) $ parsePureTermApp (PureApp tm (fst p)))
  (parseMt ts parsePureTerm2)

parseTermApp tm = ParseM $ \ ts -> case ts of
  (TDash : ts) -> maybe
    (parseMr tm ts)
    (\ p -> parseMt (snd p) $ parseTermApp (TmAppTmE tm (fst p)))
    (parseMt ts parseTerm3)
  (TCenterDot : ts) -> maybe
    (parseMr tm ts)
    (\ p -> parseMt (snd p) $ parseTermApp (TmAppTp tm (fst p)))
    (parseMt ts $ parseType2 parseTerm3)
  _ -> maybe
    (parseMr tm ts)
    (\ p -> parseMt (snd p) $ parseTermApp (TmAppTm tm (fst p)))
    (parseMt ts parseTerm3)

parseTypeApp tm tp = ParseM $ \ ts -> case ts of
  (TCenterDot : ts) -> maybe
    (parseMr tp ts)
    (\ p -> parseMt (snd p) $ parseTypeApp tm (TpAppTp tp (fst p)))
    (parseMt ts $ parseType2 tm)
  _ -> maybe
    (parseMr tp ts)
    (\ p -> parseMt (snd p) $ parseTypeApp tm (TpAppTm tp (fst p)))
    (parseMt ts tm)

parseIotaProj tm = ParseM $ \ ts -> case ts of
  (TProj1 : ts) -> parseMt ts $ parseIotaProj (IotaProj1 tm)
  (TProj2 : ts) -> parseMt ts $ parseIotaProj (IotaProj2 tm)
  _ -> parseMr tm ts

--parsePureTerm# :: ParseM PureTerm
parsePureTerm = ParseM $ \ ts -> case ts of
  (TLam : ts) -> parseMt ts $ pure PureLambda <*> parseVar <* parseDrop TDot <*> parsePureTerm
  _ -> parseMt ts parsePureTerm1
parsePureTerm1 = ParseM $ \ ts -> parseMt ts parsePureTerm2 >>= uncurry (parseMf . parsePureTermApp)
parsePureTerm2 = ParseM $ \ ts -> case ts of
  (TVar v : ts) -> parseMr (PureVar v) ts
  (TParenL : ts) -> parseMt ts $ parsePureTerm <* parseDrop TParenR
  _ -> Nothing

--parseTerm# :: ParseM Term
parseTerm = ParseM $ \ ts -> case ts of
  (TLam : ts) -> parseMt ts $ pure TmLambda <*> parseVar <* parseDrop TColon <*> parseType parseTerm3 <* parseDrop TDot <*> parseTerm
  (TLamE : ts) -> parseMt ts $ pure TmLambdaE <*> parseVar <* parseDrop TColon <*> parseTpKd parseTerm3 <* parseDrop TDot <*> parseTerm
  (TRho : ts) -> parseMt ts $ pure Rho <*> parseTerm2 <* parseDrop TAt <*> parseVar <* parseDrop TDot <*> parseType parsePureTerm2 <* parseDrop TDash <*> parseTerm
  (TPhi : ts) -> parseMt ts $ pure Phi <*> parseTerm2 <* parseDrop TDash <*> parseTerm <* parseDrop TBraceL <*> parsePureTerm <* parseDrop TBraceR
  (TDelta : ts) -> parseMt ts $ pure Delta <*> parseType2 parsePureTerm2 <* parseDrop TDash <*> parseTerm
  _ -> parseMt ts parseTerm1
parseTerm1 = ParseM $ \ ts -> parseMt ts parseTerm2 >>= uncurry (parseMf . parseTermApp)
parseTerm2 = ParseM $ \ ts -> case ts of
  (TSigma : ts) -> parseMt ts $ pure Sigma <*> parseTerm2
  _ -> parseMt ts parseTerm3
parseTerm3 = ParseM $ \ ts -> parseMt ts parseTerm4 >>= uncurry (parseMf . parseIotaProj)
parseTerm4 = ParseM $ \ ts -> case ts of
  (TVar v : ts) -> parseMr (TmVar v) ts
  (TBeta : ts) -> parseMt ts $ pure Beta <* parseDrop TAngleL <*> parsePureTerm <* parseDrop TAngleR <* parseDrop TBraceL <*> parsePureTerm <* parseDrop TBraceR
  (TParenL : ts) -> parseMt ts $ parseTerm <* parseDrop TParenR
  (TBracketL : ts) -> parseMt ts $ pure TmIota <*> parseTerm <* parseDrop TComma <*> parseTerm <* parseDrop TAt <*> parseVar <* parseDrop TDot <*> parseType parseTerm3 <* parseDrop TBracketR
  _ -> Nothing

--parseType :: ParseM tm -> ParseM (PrimType tm)
parseType tm = ParseM $ \ ts -> case ts of
  (TLam : ts) -> parseMt ts $ pure TpLambda <*> parseVar <* parseDrop TColon <*> parseTpKd tm <* parseDrop TDot <*> parseType tm
  (TAll : ts) -> parseMt ts $ pure TpAll <*> parseVar <* parseDrop TColon <*> parseTpKd tm <* parseDrop TDot <*> parseType tm
  (TPi : ts) -> parseMt ts $ pure TpPi <*> parseVar <* parseDrop TColon <*> parseType tm <* parseDrop TDot <*> parseType tm
  (TIota : ts) -> parseMt ts $ pure TpIota <*> parseVar <* parseDrop TColon <*> parseType tm <* parseDrop TDot <*> parseType tm
  _ -> parseMt ts $ parseType1 tm
parseType1 tm = ParseM $ \ ts -> parseMt ts (parseType2 tm) >>= uncurry (parseMf . parseTypeApp tm)
parseType2 tm = ParseM $ \ ts -> case ts of
  (TVar v : ts) -> parseMr (TpVar v) ts
  (TBraceL : ts) -> parseMt ts $ pure TpEq <*> parsePureTerm <* parseDrop TAsyEq <*> parsePureTerm <* parseDrop TBraceR
  (TParenL : ts) -> parseMt ts $ parseType tm <* parseDrop TParenR
  _ -> Nothing

--parseKind :: ParseM tm -> ParseM (PrimKind tm)
parseKind tm = ParseM $ \ ts -> case ts of
  (TStar : ts) -> parseMr Star ts
  (TPi : ts) -> parseMt ts $ pure KdPi <*> parseVar <* parseDrop TColon <*> parseTpKd tm <* parseDrop TDot <*> parseKind tm
  (TParenL : ts) -> parseMt ts $ parseKind tm <* parseDrop TParenR

--parseTpKd :: ParseM tm -> ParseM (PrimTpKd tm)
parseTpKd tm = parseMor (fmap TpKdTp $ parseType tm) (fmap TpKdKd $ parseKind tm)

parseCmd = ParseM $ \ ts -> case ts of
  (TVar "import" : TVar "public" : ts) -> parseMt ts $ pure ImportCmd <*> parseVar <* parseDrop TDot
  (TVar "import" : ts) -> parseMt ts $ pure ImportCmd <*> parseVar <* parseDrop TDot
  --(TImport fp : ts) -> parseMr (ImportCmd fp) ts
  (TVar v : TEq : ts) -> parseMt ts $ pure (TermCmd v) <*> parseTerm <* parseDrop TDot
  (TVar v : TTriangle : ts) -> parseMt ts $ pure (TypeCmd v) <*> parseKind parseTerm3 <* parseDrop TEq <*> parseType parseTerm3 <* parseDrop TDot
  _ -> Nothing
parseCmds = ParseM $ \ ts -> case ts of
  [] -> parseMr CmdsStart []
  _ -> parseMt ts $ pure CmdsNext <*> parseCmd <*> parseCmds

parseDropModule = ParseM $ \ ts -> case ts of
  (TVar "module" : TVar mn : TDot : ts) -> parseMr () ts
  _ -> parseMr () ts

parseStr (ParseM f) s = lexStr s >>= f
