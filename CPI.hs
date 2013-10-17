import Check
import Control.Monad.Error
import Data.Char (isSpace)
import Expand
import Norm
import Syntax.ErrM
import Syntax.AbsCP
import Syntax.LexCP
import Syntax.ParCP
import Syntax.PrintCP

import System.Console.Readline

parse p s = case p (myLexer s) of
              Bad err -> error err
              Ok p    -> p

proc = parse pProc
typ  = parse pType
ass  = parse pAssertion

chk s = case runCheck (check p) b of
          Left err -> putStrLn err
          _        -> putStrLn "ok"
    where Assert p b = ass s

n s   = normalize p b
    where Assert p b = ass s

interp :: Defns -> String -> IO Defns
interp ds s =
    case pTop (myLexer s) of
      Bad err ->
          do putStrLn err
             return ds
      Ok (TDef d) ->
          return (addDefn ds d)
      Ok (TAss (Assert p b)) ->
          case do p' <- expandP ds p
                  b' <- expandB ds b
                  runCheck (check p') b'
                  return (normalize p' b') of
            Left err ->
                do putStrLn err
                   return ds
            Right (executed, simplified) ->
                do putStrLn (unlines ["Execution results in:",
                                      printTree executed,
                                      "which can be further simplified to:",
                                      printTree simplified])
                   return ds

repl ds = do s <- readline "> "
             case trim `fmap` s of
               Nothing   -> return ()
               Just ":q" -> return ()
               Just ""   -> repl ds
               Just s'   -> addHistory s' >> interp ds s' >>= repl
    where trim = f . f
              where f = reverse . dropWhile isSpace

main = repl emptyDefns

-- For testing purposes: the first pair of Church numerals

pingZeroOne =
    add "type Church = forall X.?(X * ~X) || (~X || X)" $
    add "def Zero(x) = x(X).x(s).x(z).z<->x" $
    add "def One(x) = x(X).x(s).x(z).?s[f].f[a].(a<->z | f<->x)" $
    add "def Ping(x,y,w) = x[1].x[s].(!s(f).f(a).a().?y[u].u().f[].0 | x[z].(z[].0 | x().w[].0))" $
    emptyDefns
    where add s ds = let TDef d = parse pTop s
                     in  addDefn ds d

