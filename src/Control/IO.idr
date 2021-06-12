module Control.IO

import Builtin
import PrimIO

import Algebra.Control.Functor
import Algebra.Control.Applicative
import Algebra.Control.Monad

import Control.Console

%default total

public export
Functor IO where
  f <$> (MkIO p) = MkIO (p `prim__io_bind` (prim__io_pure . f))

  proofIdentity    = believe_me ()
  proofComposition = believe_me ()

public export
Applicative IO where
  pure x = MkIO $ prim__io_pure x
  (MkIO pf) <*> (MkIO px) = MkIO (
    pf `prim__io_bind` (\f =>
    px `prim__io_bind` (\x =>
      prim__io_pure $ f x)))

  proofIdentity     = believe_me ()
  proofHomomorphism = believe_me ()
  proofInterchange  = believe_me ()
  proofComposition  = believe_me ()

public export
Monad IO where
  (MkIO px) >>= f = MkIO (
    px `prim__io_bind` (\x =>
      let MkIO p := f x in p))

  proofLeftIdentity  = believe_me ()
  proofRightIdentity = believe_me ()
  proofAssociativity = believe_me ()

%foreign "scheme,chez:get-char (current-input-port)"
prim__getChar : PrimIO Char

%foreign "scheme,chez:get-line (current-input-port)"
prim__getLine : PrimIO String

%foreign "scheme,chez:put-char (current-output-port)"
prim__putChar : Char -> PrimIO ()

%foreign "scheme,chez:put-string (current-output-port)"
prim__putString : String -> PrimIO ()

public export
Console IO where
  getChar = MkIO prim__getChar
  getLine = MkIO prim__getLine
  putChar   c = MkIO $ prim__putChar c
  putString s = MkIO $ prim__putString s
