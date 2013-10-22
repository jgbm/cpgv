import CheckGV
import Data.Char (isSpace)
import CPBuilder
import Syntax.AbsGV
import Syntax.ErrM
import Syntax.LexGV
import Syntax.ParGV
import Syntax.PrintGV

import RunGV
import qualified Syntax.PrintCP as CP
import qualified Check as CP
import qualified Norm as CP

import System.Console.Readline

interp s = case pAssertion (myLexer s) of
             Bad err -> putStrLn err
             Ok (Assert gamma m t) ->
                 case runCheck (checkAgainst m t) gamma of
                   Left err -> putStrLn err
                   Right (p, _) -> putStrLn (unlines ["CP translation:", CP.printTree (build p),
                                                      "GV execution:", show (runProgram m)])
    where build b = fst (runBuilder b [] 0)

repl = do s <- readline "> "
          case trim `fmap` s of
            Nothing   -> return ()
            Just ":q" -> return ()
            Just ""   -> repl
            Just s'   -> addHistory s' >> interp s' >> repl
    where trim = f . f
              where f = reverse . dropWhile isSpace

main = repl
