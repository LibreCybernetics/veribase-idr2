import Builtin
import PrimIO

import Algebra.Control.Monad

import Control.Console
import Control.IO

askName : Console m => m ()
askName = do
  putLine "What's your name? "
  name <- getLine
  putString "Hello, "
  putString name
  putChar '!'
  putChar '\n'

main : IO ()
main = askName
