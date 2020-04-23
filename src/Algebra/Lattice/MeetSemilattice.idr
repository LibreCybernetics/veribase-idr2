module Algebra.Lattice.MeetSemilattice

import Builtin

import Data.Bool
import Relation.Order

%default total

infix 5 ∧

public export
interface (PartialOrder a) ⇒ MeetSemilattice a where
  (∧) : a → a → a
  proofOfCommutativity : (x, y: a) → x ∧ y = y ∧ x
  proofOfLowerBounding : (x, y: a) → IsTrue ((x ∧ y) ≤ x)
  proofOfGreatestLowerBounding: (x, y, z: a) → IsTrue (x ≤ y) → IsTrue (x ≤ z) → IsTrue (x ≤ (y ∧ z))

public export
MeetSemilattice Bool where
  (∧) = (⋄) @{BoolConjMagma}
  proofOfCommutativity = proofOfCommutativity @{BoolConjCommutativeMagma}
  proofOfLowerBounding False False = ItIsTrue
  proofOfLowerBounding False True  = ItIsTrue
  proofOfLowerBounding True  False = ItIsTrue
  proofOfLowerBounding True  True  = ItIsTrue
  proofOfGreatestLowerBounding False False False ItIsTrue ItIsTrue = ItIsTrue
  proofOfGreatestLowerBounding False False True  ItIsTrue ItIsTrue = ItIsTrue
  proofOfGreatestLowerBounding False True  False ItIsTrue ItIsTrue = ItIsTrue
  proofOfGreatestLowerBounding False True  True  ItIsTrue ItIsTrue = ItIsTrue
  proofOfGreatestLowerBounding True  False False ItIsTrue ItIsTrue impossible
  proofOfGreatestLowerBounding True  False True  ItIsTrue ItIsTrue impossible
  proofOfGreatestLowerBounding True  True  False ItIsTrue ItIsTrue impossible
  proofOfGreatestLowerBounding True  True  True  ItIsTrue ItIsTrue = ItIsTrue
