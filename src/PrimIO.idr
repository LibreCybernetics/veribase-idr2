module PrimIO

{-

Taken from Idris2 STDLIB

Copyright (c) 2019 Edwin Brady
    School of Computer Science, University of St Andrews
All rights reserved.

This code is derived from software written by Edwin Brady
(ecb10@st-andrews.ac.uk).

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions
are met:
1. Redistributions of source code must retain the above copyright
   notice, this list of conditions and the following disclaimer.
2. Redistributions in binary form must reproduce the above copyright
   notice, this list of conditions and the following disclaimer in the
   documentation and/or other materials provided with the distribution.
3. None of the names of the copyright holders may be used to endorse
   or promote products derived from this software without specific
   prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS ``AS IS'' AND ANY
EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR
PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE COPYRIGHT HOLDERS BE
LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR
BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY,
WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE
OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN
IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
-}

import Builtin

%default total

export
data IORes : Type -> Type where
  MkIORes : a -> %World -> IORes a

public export
PrimIO : Type -> Type
PrimIO a = %World -> IORes a

export
prim__io_pure : a -> PrimIO a
prim__io_pure x w = MkIORes x w

export
prim__io_bind : PrimIO a -> (a -> PrimIO b) -> PrimIO b
prim__io_bind fn k w = let MkIORes x' w' := fn w in k x' w'

unsafeCreateWorld : (%World -> a) -> a
unsafeCreateWorld f = f %MkWorld

unsafeDestroyWorld : %World -> a -> a
unsafeDestroyWorld %MkWorld x = x


public export
data IO : Type -> Type where
  MkIO : PrimIO a -> IO a

public export
unsafePerformIO : IO a -> a
unsafePerformIO (MkIO p) = unsafeCreateWorld (\w =>
  let MkIORes res w' := p w in unsafeDestroyWorld w' res)
