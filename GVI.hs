import CheckGV
import Data.Char (isSpace)
import Syntax.AbsGV
import Syntax.ErrM
import Syntax.LexGV
import Syntax.ParGV
import Syntax.PrintGV

import EvalGV

import System.Console.Readline

interp s = case pAssertion (myLexer s) of
             Bad err -> putStrLn err
             Ok (Assert gamma m t) ->
                 case runCheck (checkAgainst m t) gamma of
                   Left err -> putStrLn err
                   Right _  -> 
                     putStrLn (show $ evalProgram m)

repl = do s <- readline "> "
          case trim `fmap` s of
            Nothing   -> return ()
            Just ":q" -> return ()
            Just ""   -> repl
            Just s'   -> addHistory s' >> interp s' >> repl
    where trim = f . f
              where f = reverse . dropWhile isSpace

main = repl
