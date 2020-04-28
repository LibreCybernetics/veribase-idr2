module Algebra.Ring.Ring

import Builtin

import public Algebra.Ring.Semiring

infix 5 -

public export
interface (Semiring a) ⇒ Ring a where
  sumInv : a → a
  proofOfLeftSumInverse  : (x: a) → (sumInv x) + x = Semiring.zero
  proofOfRightSumInverse : (x: a) → x + (sumInv x) = Semiring.zero

public export
(-) : (Ring a) ⇒ a → a → a
x - y = x + (sumInv y)
