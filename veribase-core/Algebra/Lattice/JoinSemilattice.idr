module Algebra.Lattice.JoinSemilattice

import Builtin

import Data.Bool
import Relation.Order

%default total

infix 5 ∨

public export
interface (Order a) ⇒ JoinSemilattice a where
  (∨) : a → a → a
  proofOfCommutativity : (x, y: a) → x ∨ y = y ∨ x
  proofOfUpperBounding : (x, y: a) → IsTrue (x ≤ (x ∨ y))
  proofOfLeastUpperBounding: (x, y, z: a) → IsTrue (x ≤ z) → IsTrue (y ≤ z) → IsTrue ((x ∨ y) ≤ z)

public export
interface (JoinSemilattice a) ⇒ BoundedJoinSemilattice a where
  lowerBound : a
  proofOfLowerBound: (x: a) → IsTrue (lowerBound ≤ x)

public export
JoinSemilattice Bool where
  (∨) = (⋄) @{BoolDisjMagma}
  proofOfCommutativity = proofOfCommutativity @{BoolDisjCommutativeMagma}
  proofOfUpperBounding False False = ItIsTrue
  proofOfUpperBounding False True  = ItIsTrue
  proofOfUpperBounding True  False = ItIsTrue
  proofOfUpperBounding True  True  = ItIsTrue

  proofOfLeastUpperBounding False False False ItIsTrue ItIsTrue = ItIsTrue
  proofOfLeastUpperBounding False False True  ItIsTrue ItIsTrue = ItIsTrue
  proofOfLeastUpperBounding False True  False ItIsTrue ItIsTrue impossible
  proofOfLeastUpperBounding False True  True  ItIsTrue ItIsTrue = ItIsTrue
  proofOfLeastUpperBounding True  False False ItIsTrue ItIsTrue impossible
  proofOfLeastUpperBounding True  False True  ItIsTrue ItIsTrue = ItIsTrue
  proofOfLeastUpperBounding True  True  False ItIsTrue ItIsTrue impossible
  proofOfLeastUpperBounding True  True  True  ItIsTrue ItIsTrue = ItIsTrue

public export
BoundedJoinSemilattice Bool where
  lowerBound = False
  proofOfLowerBound False = ItIsTrue
  proofOfLowerBound True  = ItIsTrue
