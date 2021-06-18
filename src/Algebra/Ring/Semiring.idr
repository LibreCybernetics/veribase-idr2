module Algebra.Ring.Semiring

import Builtin

import Algebra.Group.Magma
import Algebra.Group.Monoid

infixl 5 +
infixl 6 *

public export
interface Semiring t where
  (+) : t -> t -> t
  (*) : t -> t -> t

  zero : t
  one  : t

  proofSumZero : (x : t) -> x + zero = x
  proofSumCommutative : (x, y : t) -> x + y = y + x
  proofSumAssociative : (x, y, z : t) -> x + (y + z) = (x + y) + z

  proofMultOneLeft  : (x : t) -> one * x = x
  proofMultOneRight : (x : t) -> x * one = x
  proofMultAssociative : (x, y, z : t) -> x * (y * z) = (x * y) * z

  proofMultDistributesSumLeft : (x, y, z : t) -> x * (y + z) = x * y + x * z
  proofMultDistributesSumRight : (x, y, z : t) -> (x + y) * z = x * z + y * z

  zeroAnnihilatorLeft : (x : t) -> zero * x = zero
  zeroAnnihilatorRight : (x : t) -> x * zero = zero
