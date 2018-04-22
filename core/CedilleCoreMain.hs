module Main where
import CedilleCoreCheck
import CedilleCoreCtxt
import CedilleCoreNorm
import CedilleCoreParser hiding (main)
import CedilleCoreLexer hiding (main)
import CedilleCoreToString
import CedilleCoreTypes


--checkCmd :: Cmd -> Ctxt -> Either String Ctxt
checkCmd (TermCmd v tm) c = synthTerm c tm >>= \ tp -> Right (ctxtDefTerm c v (Just (hnfeTerm c tm), Just (hnfType c tp)))
checkCmd (TypeCmd v tp) c = synthType c tp >>= \ kd -> Right (ctxtDefType c v (Just (hnfeType c tp), Just (hnfKind c kd)))

--checkCmds :: Cmds -> Ctxt -> Either String Ctxt
checkCmds CmdsStart ctxt = Right ctxt
checkCmds (CmdsNext c cs) ctxt = checkCmd c ctxt >>= checkCmds cs

--fileParsed :: Ctxt -> Either (Either String String) Cmds -> IO Ctxt
fileParsed c (Left (Left le)) = putStrLn ("Lexing error at position " ++ le) >> return c
fileParsed c (Left (Right pe)) = putStrLn ("Parsing error at position " ++ pe) >> return c
fileParsed c (Right cs) = case checkCmds cs c of
  (Left err) -> putStrLn err >> return c
  (Right c') -> putStrLn "No errors" >> return c'

--splitStr :: String -> String -> [String]
splitStr s [] = s : []
splitStr s (' ' : cs) = s : splitStr "" cs
splitStr s (c : cs) = splitStr (s ++ (c : [])) cs

--joinStr :: [String] -> String
joinStr [] = ""
joinStr (s : []) = s
joinStr (s : ss) = s ++ " " ++ joinStr ss

--handleInput :: Ctxt -> [String] -> IO ()
handleInput c ("check" : fp) = readFile (joinStr fp) >>= fileParsed c . parseStr >>= mainWithCtxt
handleInput c ("lookup" : "term" : "hnf" : v : []) = putStrLn (maybe "Term not defined" show (ctxtLookupTermVar c v)) >> mainWithCtxt c
handleInput c ("lookup" : "type" : "hnf" : v : []) = putStrLn (maybe "Type not defined" show (ctxtLookupTypeVar c v)) >> mainWithCtxt c
handleInput c ("lookup" : "term" : "type" : v : []) = putStrLn (maybe "Term not defined" show (ctxtLookupVarType c v)) >> mainWithCtxt c
handleInput c ("lookup" : "type" : "kind" : v : []) = putStrLn (maybe "Type not defined" show (ctxtLookupVarKind c v)) >> mainWithCtxt c
handleInput c ("restart" : []) = mainWithCtxt emptyCtxt
handleInput c ("quit" : []) = return ()
handleInput c _ = putStrLn "Unknown command" >> mainWithCtxt c

mainWithCtxt c = getLine >>= handleInput c . splitStr ""

main = mainWithCtxt emptyCtxt
