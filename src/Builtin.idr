module Builtin

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

%default total

infixr 9 .
infixr 8 $

-- Tuples

public export
data Pair : Type -> Type -> Type where
  MkPair : {a, b : Type} -> (x : a) -> (y : b) -> Pair a b

public export
fst : (a, b) -> a
fst (x, _) = x

public export
snd : (a, b) -> b
snd (_, y) = y

-- Utility

public export
identity : a -> a
identity x = x

public export
the : (0 t : Type) -> (a : t) -> t
the _ x = x

public export
const : (x : a) -> ((0 _ : b) -> a)
const x = \_ => x

public export
($) : (a -> b) -> a -> b
($) f x = f x

public export
flip : (f : a -> b -> c) -> b -> a -> c
flip f x y = f y x

public export
(.) : (b -> c) -> (a -> b) -> a -> c
(.) f g = \x => f (g x)

-- Assertions

public export
believe_me : a -> b
believe_me = prim__believe_me _ _

public export
assert_total : a -> a
assert_total = identity

-- Equality

public export
data Equal : a -> b -> Type where
  Refl : {x : a} -> Equal x x

%name Equal prf

infix 9 ===, ~=~

public export
(===) : (x : a) -> (y : a) -> Type
(===) = Equal

public export
(~=~) : (x : a) -> (y : b) -> Type
(~=~) = Equal

-- Void/Uninhabited

public export
data Void : Type where

public export %extern
void : (0 v : Void) -> a

public export
interface Uninhabited t where
  uninhabited : t -> Void

export
Uninhabited Void where
  uninhabited = identity

public export
absurd : Uninhabited t => (h : t) -> a
absurd h = void (uninhabited h)

-- Decidable

public export
data Dec : Type -> Type where
  Yes : (prf : prop)         -> Dec prop
  No  : (ctr : prop -> Void) -> Dec prop

-- Rewrite

public export %inline
rewrite__impl : {0 x, y : a} -> (0 p : _) -> (0 rule : x = y) -> (1 val : p y)
              -> p x
rewrite__impl p Refl prf = prf

%rewrite Equal rewrite__impl

public export %inline
replace : forall x, y, p . (0 rule : x = y) -> p x -> p y
replace Refl prf = prf
