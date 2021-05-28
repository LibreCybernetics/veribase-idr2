module Algebra.Monad

import Builtin

import Algebra.Applicative

%default total

public export
interface Applicative t => Monad t where
  bind : t a -> (a -> t b) -> t b

  proofLeftIdentity : (x : a) -> (f : a -> t b) -> Applicative.pure x `bind` f = f x
  proofRightIdentity : (x : t a) -> x `bind` Applicative.pure = x
  proofAssociativity : (x : t a) -> (f : a -> t b) -> (g : b -> t c)
                     -> (x `bind` f) `bind` g = x `bind` (\x => f x `bind` g)
