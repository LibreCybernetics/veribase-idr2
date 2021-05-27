module Algebra.Applicative

import Builtin

import Algebra.Functor

%default total

infixr 8 <*>

public export
interface Functor t => Applicative t where
  pure : a -> t a
  (<*>) : t (a -> b) -> t a -> t b

  proofIdentity : (x : t a) -> pure Builtin.identity <*> x = x
  proofHomomorphism : (f : a -> b) -> (x : a) -> pure f <*> pure x = pure (f x)
  proofInterchange : (f : t (a -> b)) -> (x : a) -> f <*> pure x = pure ($ x) <*> f
  proofComposition : (f : t (a -> b)) -> (g : t (b -> c)) -> (x : t a)
                   ->  ((pure Builtin.(.) <*> g) <*> f) <*> x = g <*> f <*> x
