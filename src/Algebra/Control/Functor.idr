module Algebra.Control.Functor

import Builtin

%default total

public export
interface Functor t where
  map : (a -> b) -> t a -> t b

  proofIdentity : (x : t a) -> map Builtin.identity x = x
  proofComposition : (f : a -> b) -> (g : b -> c) -> (x : t a) -> map (g . f) x = map g . map f $ x
