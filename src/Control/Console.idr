module Control.Console

import public Builtin

%default total

public export
interface Console t where
  getChar : t Char
  getLine : t String
  putChar : Char -> t ()
  putString : String -> t ()

public export
putLine : Console t => String -> t ()
putLine = putString -- TODO: Append newline
