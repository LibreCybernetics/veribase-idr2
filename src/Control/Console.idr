module Control.Console

import Builtin

import Algebra.Control.Monad

%default total

public export
interface Monad t => Console t where
  getChar : t Char
  getLine : t String
  putChar : Char -> t ()
  putString : String -> t ()

public export
putLine : Console t => String -> t ()
putLine = putString -- TODO: Append newline
