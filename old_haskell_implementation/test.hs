{-# LANGUAGE QuasiQuotes #-}

import Core

main :: IO ()
main = do

  src <- readFile "./test.ced"

  putStrLn "[Term]"
  putStrLn . toString . fromString $ src
  putStrLn ""

  putStrLn "[Normal]"
  putStrLn . toString . norOf . annotate . fromString $ src
  putStrLn ""

  putStrLn "[Type]"
  putStrLn . toString . typOf . annotate . fromString $ src
  putStrLn ""
