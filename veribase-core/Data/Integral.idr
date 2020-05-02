module Data.Integral

import Builtin

import Algebra.Ring.Semiring
import Data.Bool
import Relation.Equiv
import Relation.Order

%default total

%integerLit fromInteger


-- TODO: Add restrictions to remove Semiring.zero from the domains of div/mod.
-- Upstream: https://github.com/edwinb/Idris2/issues/336
public export
interface (Semiring a, StrictTotalOrder a) ⇒ Integral a where
  fromInteger : Integer → a
  divMod : (n, d: a) → (a, a)

public export
div : Integral a ⇒ (n, d: a) → a
div x y = fst $ divMod x y

public export
mod : Integral a ⇒ (n, d: a) → a
mod x y = snd $ divMod x y

public export
divBy : (Integral a) ⇒ (n, d: a) → Bool
divBy x y = (x `mod` y) ≡ zero
