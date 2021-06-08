module Control.IO

import public PrimIO

import Algebra.Control.Functor
import Algebra.Control.Applicative
import Algebra.Control.Monad

import Control.Console

%default total

public export
data IO : Type -> Type where
  MkIO : PrimIO a -> IO a

public export
Functor IO where
  map f (MkIO p) = MkIO (p `prim__io_bind` (prim__io_pure . f))

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
  bind (MkIO px) f = MkIO (
    px `prim__io_bind` (\x =>
      let MkIO p := f x in p))

  proofLeftIdentity  = believe_me ()
  proofRightIdentity = believe_me ()
  proofAssociativity = believe_me ()

%foreign "C:getchar,libc 6"
%extern
prim__getChar : PrimIO Char

%foreign "C:idris2_getStr, libidris2_support, idris_support.h"
%extern
prim__getStr : PrimIO String

%foreign "C:putchar,libc 6"
%extern
prim__putChar : Char -> PrimIO ()

%foreign "C:idris2_putStr, libidris2_support, idris_support.h"
%extern
prim__putStr : String -> PrimIO ()

public export
Console IO where
  getChar = MkIO prim__getChar
  getLine = MkIO prim__getStr
  putChar   c = MkIO $ prim__putChar c
  putString s = MkIO $ prim__putStr s
