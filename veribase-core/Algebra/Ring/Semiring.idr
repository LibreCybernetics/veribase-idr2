module Algebra.Ring.Semiring

import Builtin

%default total

infix 5 +, ⋅

public export
interface Semiring a where
  (+) : a → a → a
  (⋅) : a → a → a
  zero : a
  one  : a
  proofOfSumAssociativity : (x, y, z: a) → x + (y + z) = (x + y) + z
  proofOfSumLeftIdentity : (x: a) → zero + x = x
  proofOfSumRightIdentity : (x: a) → x + zero = x
  proofOfProdAssociativity : (x, y, z: a) → x ⋅ (y ⋅ z) = (x ⋅ y) ⋅ z
  proofOfProdLeftIdentity : (x: a) → one ⋅ x = x
  proofOfProdRightIdentity : (x: a) → x ⋅ one = x
