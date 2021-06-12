module Algebra.Control.Functor

import Builtin

%default total

infixl 9 <$>

public export
interface Functor t where
  (<$>) : (a -> b) -> t a -> t b

  proofIdentity : (x : t a) -> Builtin.identity <$> x = x
  proofComposition : (f : a -> b) -> (g : b -> c) -> (x : t a)
                   -> (g . f) <$> x = (g <$>) . (f <$>) $ x
