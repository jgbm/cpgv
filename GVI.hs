import CheckGV
import Data.Char (isSpace)
import CPBuilder
import Syntax.AbsGV
import Syntax.ErrM
import Syntax.LexGV
import Syntax.ParGV
import Syntax.PrintGV

import RunGV
import qualified Syntax.AbsCP as CP
import qualified Syntax.PrintCP as CP
import qualified Check as CP
import qualified Norm as CP

import System.Console.Readline

interp s = case pAssertion (myLexer s) of
             Bad err -> putStrLn err
             Ok (Assert gamma m t) ->
                 case runCheck (checkAgainst m t) gamma of
                   Left err -> putStrLn err
                   Right (p, _) -> let p' = build p
                                       cpBehavior = CP.Typing (CP.LIdent "z'0") (xType t) :
                                                    [CP.Typing (CP.LIdent v) (CP.dual (xType t)) | Typing (LIdent v) t <- gamma]
                                       cpResults = case CP.runCheck (CP.check p') cpBehavior of
                                                     Left err -> unlines ["CP translation:", CP.printTree (CP.Assert p' cpBehavior), "But:", err]
                                                     Right _  -> let (normalized, simplified) = CP.normalize p' cpBehavior
                                                                 in unlines ["CP translation:", CP.printTree (CP.Assert p' cpBehavior),
                                                                             "CP normalization:", CP.printTree normalized,
                                                                             "CP simplification:", CP.printTree simplified]
                                       gvResults | null gamma = unlines ["GV execution:", show (runProgram m)]
                                                 | otherwise  = "No GV execution (free variables).\n"
                                   in putStrLn (gvResults ++ cpResults)
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
