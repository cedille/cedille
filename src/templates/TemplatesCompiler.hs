module Main where
import System.Directory
import System.FilePath
import qualified Data.Text
import qualified CedilleParser

templatesDir = "src" </> "templates"
outputFile = "src" </> "templates.agda"

writeMsg = appendFile outputFile . flip (++) "\n"
writeHdr =
  writeFile outputFile "" >>
  writeMsg "module templates where" >>
  writeMsg "open import lib" >>
  writeMsg "open import cedille-types"

mapio f = flip foldr (return []) $
  \ a xsio -> f a >>= \ x -> xsio >>= return . (:) x

readFiles = mapio $ \ f -> readFile f >>= \ fc -> return (f, fc)
addPfxs = map $ (</>) templatesDir
getCedFiles = filter $ \ f -> takeExtension f == ".ced"
parseStrings = map $ \ (f, fc) ->
  (f, CedilleParser.parseTxt $ Data.Text.pack fc)

errMsg f (Left p) =
  "Lexical error in file " ++ f ++ " at position " ++ Data.Text.unpack p
errMsg f (Right p) =
  "Parse error in file " ++ f ++ " at position " ++ Data.Text.unpack p

writeMsgs =
  flip foldl (return ()) $ \ x (f, p) ->
    flip (either (error . errMsg f)) p $ \ pt ->
      writeMsg ("\n\n" ++ takeBaseName f ++ "Template = " ++ show pt) >> x

main =
  writeHdr >>
  getDirectoryContents templatesDir >>=
  readFiles . addPfxs . getCedFiles >>=
  writeMsgs . parseStrings
