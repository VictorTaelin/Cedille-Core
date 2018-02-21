import System.Environment
import Core

main :: IO ()
main = do

  args <- System.Environment.getArgs

  case args of
    [] ->
      do
        putStrLn "Run with the name of one Cedille-Core file to process."
    file : _ ->
      do
        src <- readFile file

        putStrLn "[Term]"
        putStrLn . toString . fromString $ src
        putStrLn ""

        putStrLn "[Normal]"
        putStrLn . toString . norOf . annotate . fromString $ src
        putStrLn ""

        putStrLn "[Type]"
        putStrLn . toString . typOf . annotate . fromString $ src
        putStrLn ""
