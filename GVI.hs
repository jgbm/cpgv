import Control.Monad.Trans
import Data.Char (isSpace)
import Data.List (partition)
import GV.Check
import GV.CPBuilder
import GV.Parser
import GV.Printer
import GV.Run
import GV.Scope
import GV.Syntax

import qualified CP.Syntax as CP
import qualified CP.Printer as CP
import qualified CP.Check as CP
import qualified CP.Norm as CP

import System.Console.Haskeline
import System.Environment (getArgs)

interp (Assert gamma m t) =
    case runCheck (checkAgainst (renameTerm m) t) gamma of
      Left err -> putStrLn err
      Right (p, _) -> let p' = build p
                          showCP c = (displayS (renderPretty 0.8 120 (pretty c))) ""
                          cpBehavior = ("z'0", xType t) :
                                       [(v, CP.dual (xType t)) | (v, t) <- gamma]
                          cpResults = case CP.runCheck (CP.check p') (cpBehavior, []) of
                                        (_, Left err) -> unlines ["CP translation:", showCP (CP.Assert p' cpBehavior False), "But:", err]
                                        (_, Right _)  -> let Right (normalized, simplified) = CP.runM (CP.normalize p')
                                                         in unlines ["CP translation:", showCP (CP.Assert p' cpBehavior False) {-,
                                                                     "CP normalization:", showCP normalized,
                                                                     "CP simplification:", showCP  simplified -}]
                          gvResults | null gamma = unlines ["GV execution:", show (runProgram m)]
                                    | otherwise  = "No GV execution (free variables).\n"
                      in putStrLn (gvResults ++ cpResults)
    where build b = fst (runBuilder b [] 0)

repl = do s <- getInputLine "> "
          case trim `fmap` s of
            Nothing   -> return ()
            Just ":q" -> return ()
            Just ""   -> repl
            Just s'   -> case parse prog s' of
                           Left err -> outputStrLn err >> repl
                           Right as -> liftIO (mapM_ interp as) >> repl
    where trim = f . f
              where f = reverse . dropWhile isSpace


interpFile fn =
    do s <- readFile fn
       case parse prog s of
         Left err -> do putStrLn ("When parsing " ++ fn)
                        putStrLn err
         Right as -> mapM_ interp as

main = do args <- getArgs
          let (interactive, files) = partition ("-i" ==) args
          mapM_ interpFile files
          if not (null interactive) || null files then runInputT defaultSettings repl else return ()
