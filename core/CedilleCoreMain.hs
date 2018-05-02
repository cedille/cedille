module Main where
import CedilleCoreCheck
import CedilleCoreCtxt
import CedilleCoreNorm
import CedilleCoreParser
import CedilleCoreToString
import CedilleCoreTypes


--checkCmd :: Cmd -> Ctxt -> Either String Ctxt
checkCmd (TermCmd v tm) c =
    if ctxtBindsVar c v then Left ("Multiple definitions of variable " ++ v) else Right () >>
    synthTerm c tm >>= \ tp ->
    Right (ctxtDefTerm c v (Just (hnfeTerm c tm), Just (hnfType c tp)))
checkCmd (TypeCmd v kd tp) c =
  if ctxtBindsVar c v then Left ("Multiple definitions of variable " ++ v) else Right () >>
  synthType c tp >>= \ kd' ->
  errIfNot (convKind c (eraseKind kd) kd') ("The expected kind does not match the synthesized kind, in the definition of " ++ v) >>
  Right (ctxtDefType c v (Just (hnfeType c tp), Just (hnfKind c kd')))

--checkCmds :: Cmds -> Ctxt -> Either String Ctxt
checkCmds CmdsStart ctxt = Right ctxt
checkCmds (CmdsNext c cs) ctxt = checkCmd c ctxt >>= checkCmds cs

--fileParsed :: Ctxt -> String -> IO Ctxt
parseFile c s = maybe
  (putStrLn "Parse error" >> return c)
  (\ cs -> case checkCmds (fst cs) c of
    (Left err) -> putStrLn err >> return c
    (Right c') -> putStrLn "No errors" >> return c')
  (lexStr s >>= parseMf parseCmds)

--splitStr :: String -> String -> [String]
splitStr s [] = s : []
splitStr s (' ' : cs) = s : splitStr "" cs
splitStr s (c : cs) = splitStr (s ++ (c : [])) cs

--joinStr :: [String] -> String
joinStr [] = ""
joinStr (s : []) = s
joinStr (s : ss) = s ++ " " ++ joinStr ss

--handleInput :: Ctxt -> [String] -> IO ()
handleInput c ("check" : fp) = readFile (joinStr fp) >>= parseFile c >>= mainWithCtxt
handleInput c ("lookup" : "term" : "hnf" : v : []) = putStrLn (maybe "Term not defined" show (ctxtLookupTermVar c v)) >> mainWithCtxt c
handleInput c ("lookup" : "type" : "hnf" : v : []) = putStrLn (maybe "Type not defined" show (ctxtLookupTypeVar c v)) >> mainWithCtxt c
handleInput c ("lookup" : "term" : "type" : v : []) = putStrLn (maybe "Term not defined" show (ctxtLookupVarType c v)) >> mainWithCtxt c
handleInput c ("lookup" : "type" : "kind" : v : []) = putStrLn (maybe "Type not defined" show (ctxtLookupVarKind c v)) >> mainWithCtxt c
handleInput c ("restart" : []) = mainWithCtxt emptyCtxt
handleInput c ("quit" : []) = return ()
handleInput c _ = putStrLn "Unknown command" >> mainWithCtxt c

mainWithCtxt c = getLine >>= handleInput c . splitStr ""

main = mainWithCtxt emptyCtxt
