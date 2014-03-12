module CPI where

import Control.Monad.Error
import Data.Char (isSpace)
import Data.IORef
import Data.List (partition)
import CP.Check
import CP.Expand
import CP.Norm hiding (trace)
import CP.Syntax
import CP.Printer
import CP.Parser
import System.Console.Haskeline
import System.Environment (getArgs)

import GV.Printer
import CPToGV
import qualified GV.Syntax as GV
import qualified GV.Check as GV

import CP.Trace

traceBehavior i b =
    case b of
      [] -> si ++ "{}"
      (t:ts) -> unlines ((si ++ st t) : [sp ++ st t | t <- ts])
    where si = '(' : show i ++ ") "
          sp = replicate (length si) ' '
          st (v, t) =  takeWhile ('\'' /=) v ++ ": " ++ showCP t
          showCP x = (displayS . renderPretty 0.8 120 . pretty) x ""

into (t, Left err) = throwError (unlines ([traceBehavior i b | (i, b) <- zip [1..] t] ++ [err]))
into (t, Right v)  = return t

interp ds (Left d) = return (addDefn ds d)
interp ds (Right (Assert p b isCheck)) =
    case runM $ do (p', b') <- expandTop ds p b
                   t <- -- trace ("Expanded " ++ showCP (Assert p b isCheck) ++ "\nto:" ++ showCP (Assert p' b' isCheck)) $
                        into (runCheck (check p') (b', []))
                   (executed, simplified) <- if isCheck then return (undefined, undefined) else normalize p'
                   return (p', t, b', executed, simplified) of
      Left err ->
          do if isCheck then putStrLn ("Check failed: " ++ show (pretty (Assert p b isCheck))) else return ()
             putStrLn err
             return ds
      Right (p', t, b', executed, simplified)
          | isCheck ->
              do sequence_ [putStrLn (traceBehavior i b) | (i, b) <- zip [1..] t]
                 return ds
          | otherwise ->
              let gvContext = [(v, xType t) | (v, t) <- b']
                  gvExpr    = xTerm [(v, t) | (v, t) <- b'] p'
                  gvResult | any (not . hasGVTranslation . snd) b' || not (hasGVTranslation p') =
                              ["CP expression has no GV translation."]
                           | otherwise =
                              ["GV translation is: ", displayS (renderPretty 0.8 120 (pretty (GV.Assert gvContext gvExpr (GV.Lift GV.OutTerm)))) ""] ++
                              (case GV.runCheck (GV.checkAgainst gvExpr (GV.Lift GV.OutTerm)) gvContext of
                                 Left err -> ["which is ill-typed:", err]
                                 Right _  -> [])

              in  do sequence_ [putStrLn (traceBehavior i b) | (i, b) <- zip [1..] t]
                     putStrLn (unlines (["Execution results in:",
                                         displayS (renderPretty 0.8 120 (pretty executed)) "",
                                         "which can be further simplified to:",
                                         displayS (renderPretty 0.8 120 (pretty simplified)) ""] ++
                                        gvResult))
                     return ds

repl ds = do s <- getInputLine "> "
             case trim `fmap` s of
               Nothing   -> return ()
               Just ":q" -> return ()
               Just ""   -> repl ds
               Just ('-' : '-' : _) -> repl ds
               Just s'   -> case parse tops s' of
                              Left err -> do outputStrLn err
                                             repl ds
                              Right ts -> liftIO (foldM interp ds ts) >>= repl
    where trim = f . f
              where f = reverse . dropWhile isSpace

parseFile ds fn =
    do s <- readFile fn
       case parse tops s of
         Left err -> do putStrLn err
                        return ds
         Right ts -> foldM interp ds ts

main = do args <- getArgs
          let (interactive, rest) = partition ("-i" ==) args
          let (enableTracing, files) = partition ("-t" ==) rest
          when (not (null enableTracing)) (writeIORef doTrace True)
          ds <- foldM parseFile emptyDefns files
          if not (null interactive) || null files then runInputT defaultSettings (repl ds) else return ()
