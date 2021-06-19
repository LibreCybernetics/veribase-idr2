module Data.LinkedList.Monad

import Builtin

import Algebra.Control.Applicative
import Algebra.Control.Monad

import public Data.LinkedList.Basic
import public Data.LinkedList.Applicative

%default total

public export
Monad LinkedList where
  Nil >>= _ = Nil
  (x::xs) >>= f = f x `concat` (xs >>= f)

  proofLeftIdentity x f = rewrite proofConcatRightIdentity (f x) in Refl

  proofRightIdentity Nil = Refl
  proofRightIdentity (x::xs) with (Monad.proofRightIdentity xs)
    proofRightIdentity (_::_) | prf = rewrite prf in Refl

  proofAssociative Nil f g = Refl
  proofAssociative (x::xs) f g = case f x of
    Nil     => ?holeAssociative1
    (r::rs) => ?holeAssociative2
