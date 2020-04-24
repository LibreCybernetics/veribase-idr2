module Algebra.BooleanAlgebra

import Builtin

import Algebra.Lattice.Lattice
import Data.Bool

%default total

public export
interface (BoundedDistributiveLattice a) ⇒ BooleanAlgebra a where
  ¬ : a → a
  proofOfJoinComplement : (x: a) → x ∨ ¬ x = MeetSemilattice.upperBound
  proofOfMeetComplement : (x: a) → x ∧ ¬ x = JoinSemilattice.lowerBound

public export
BooleanAlgebra Bool where
  ¬ False = True
  ¬ True  = False

  proofOfJoinComplement False = Refl
  proofOfJoinComplement True  = Refl

  proofOfMeetComplement False = Refl
  proofOfMeetComplement True  = Refl
