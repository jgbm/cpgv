import CheckGV
import Data.Char (isSpace)
import Syntax.AbsGV
import Syntax.ErrM
import Syntax.LexGV
import Syntax.ParGV
import Syntax.PrintGV

import System.Console.Readline

interp s = case pAssertion (myLexer s) of
             Bad err -> putStrLn err
             Ok (Assert gamma m t) ->
                 case runCheck (check m t) (empty, gamma, 1) of
                   Left err -> putStrLn err
                   Right _  -> putStrLn "ok"

repl = do s <- readline "> "
          case trim `fmap` s of
            Nothing   -> return ()
            Just ":q" -> return ()
            Just ""   -> repl
            Just s'   -> addHistory s' >> interp s' >> repl
    where trim = f . f
              where f = reverse . dropWhile isSpace

main = repl