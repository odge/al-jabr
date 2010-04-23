module AlJabr where

import Prelude hiding ((+),(-),(*),(/),(^))
import System.Console.Haskeline
import Text.ParserCombinators.Parsec

import Operations
import Numbers
import Polynomials
import Syntax

main :: IO ()
main = runInputT defaultSettings loop
   where 
       loop :: InputT IO ()
       loop = do
           minput <- getInputLine "] "
           case minput of
               Nothing -> return ()
               Just "quit" -> return ()
               Just input -> do iteration input
                                loop
       iteration input = do
         case parse term [] input :: Either ParseError (Term Algebraic) of
           Left parseError -> do outputStrLn "Parse error:" ; outputStrLn $ show parseError
           Right result -> outputStrLn $ show result

