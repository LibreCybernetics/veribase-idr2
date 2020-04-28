module Builtin

{-
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

infixr 9 ∘
infixr 8 $

-- Touples

public export
data Pair : Type → Type → Type where
  MkPair : {a, b : Type} → (x : a) → (y : b) → Pair a b

-- Utility

public export
%inline
id : (1 x : a) → a
id x = x

public export
%inline
the : (0 t : Type) → (1 v : t) → t
the _ v = v

public export
($) : (f: a → b) → a → b
($) f x = f x

public export
flip : (f : a → b → c) → b → a → c
flip f x y = f y x

public export %inline
(∘) : (b → c) → (a → b) → a → c
(∘) f g = \x => f (g x)

-- Equality

public export
data Equal : a → b → Type where
     Refl : {x : a} → Equal x x

%name Equal prf

infix 9 ===, ~=~

public export
(===) : (x : a) → (y : a) → Type
(===) = Equal

public export
(~=~) : (x : a) → (y : b) → Type
(~=~) = Equal

-- Void/Uninhabited

public export
data Void : Type where

public export
interface Uninhabited t where
  uninhabited : t → Void

%extern
public export
void : (0 x : Void) → a

export
Uninhabited Void where
  uninhabited = id

public export
absurd : Uninhabited t => (h : t) → a
absurd h = void (uninhabited h)

-- Rewrite

%inline
public export
rewrite__impl : {0 x, y : a} → (0 p : _) →
                (0 rule : x = y) → (1 val : p y) → p x
rewrite__impl p Refl prf = prf

%rewrite Equal rewrite__impl

%inline
public export
replace : forall x, y, p . (0 rule : x = y) → p x → p y
replace Refl prf = prf
