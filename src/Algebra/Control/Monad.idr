module Algebra.Control.Monad

import Builtin

import Algebra.Control.Applicative

%default total

infixl 1 >>=, >>

public export
interface Applicative t => Monad t where
  (>>=) : t a -> (a -> t b) -> t b

  proofLeftIdentity : (x : a) -> (f : a -> t b) -> Applicative.pure x >>= f = f x
  proofRightIdentity : (x : t a) -> x >>= Applicative.pure = x
  proofAssociative : (x : t a) -> (f : a -> t b) -> (g : b -> t c)
                     -> (x >>= f) >>= g = x >>= (\x => f x >>= g)

public export
(>>) : Monad t => t a -> t b -> t b
mx >> my = (mx >>= (\_ => my))
