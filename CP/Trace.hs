module CP.Trace where

import Control.Monad
import Data.IORef
import qualified Debug.Trace as Trace
import System.IO.Unsafe

{-# NOINLINE doTrace #-}
doTrace = unsafePerformIO (newIORef False)

trace s x = unsafePerformIO (do b <- readIORef doTrace
                                when b (Trace.traceIO s)
                                return x)
