
import Distribution.Simple
import Distribution.Simple.LocalBuildInfo
import Distribution.Simple.Setup
import Distribution.PackageDescription
import System.Process

main :: IO ()
main = defaultMainWithHooks userhooks

userhooks :: UserHooks
userhooks = simpleUserHooks { buildHook = buildHook' }

buildHook' :: PackageDescription -> LocalBuildInfo -> UserHooks -> BuildFlags -> IO ()
buildHook' pd lbi hooks flags = do
    -- Use make to resolve dependencies and prevent repeat code gen
    output <- readProcess "make" ["cedille-cabal"] ""
    putStrLn output
    buildHook simpleUserHooks pd lbi hooks flags
