module Algebra.Lattice.Lattice

import Builtin

import Algebra.Lattice.JoinSemilattice
import Algebra.Lattice.MeetSemilattice
import Data.Bool

%default total

public export
interface (JoinSemilattice a, MeetSemilattice a) ⇒ Lattice a where
  proofOfJoinAbsorbsMeet : (x, y: a) → x ∨ (x ∧ y) = x
  proofOfMeetAbsorbsJoin : (x, y: a) → x ∧ (x ∨ y) = x

public export
interface (BoundedJoinSemilattice a, BoundedMeetSemilattice a, Lattice a) ⇒ BoundedLattice a where

public export
interface Lattice a ⇒ DistributiveLattice a where
  proofOfJoinDistributesMeet : (x, y, z: a) → x ∨ (y ∧ z) = (x ∨ y) ∧ (x ∨ z)
  proofOfMeetDistributesJoin : (x, y, z: a) → x ∧ (y ∨ z) = (x ∧ y) ∨ (x ∧ z)

public export
interface (BoundedLattice a, DistributiveLattice a) ⇒ BoundedDistributiveLattice a where

public export
Lattice Bool where
  proofOfJoinAbsorbsMeet False False = Refl
  proofOfJoinAbsorbsMeet False True  = Refl
  proofOfJoinAbsorbsMeet True  False = Refl
  proofOfJoinAbsorbsMeet True  True  = Refl

  proofOfMeetAbsorbsJoin False False = Refl
  proofOfMeetAbsorbsJoin False True  = Refl
  proofOfMeetAbsorbsJoin True  False = Refl
  proofOfMeetAbsorbsJoin True  True  = Refl

public export
BoundedLattice Bool where

public export
DistributiveLattice Bool where
  proofOfJoinDistributesMeet False False False = Refl
  proofOfJoinDistributesMeet False False True  = Refl
  proofOfJoinDistributesMeet False True  False = Refl
  proofOfJoinDistributesMeet False True  True  = Refl
  proofOfJoinDistributesMeet True  False False = Refl
  proofOfJoinDistributesMeet True  False True  = Refl
  proofOfJoinDistributesMeet True  True  False = Refl
  proofOfJoinDistributesMeet True  True  True  = Refl

  proofOfMeetDistributesJoin False False False = Refl
  proofOfMeetDistributesJoin False False True  = Refl
  proofOfMeetDistributesJoin False True  False = Refl
  proofOfMeetDistributesJoin False True  True  = Refl
  proofOfMeetDistributesJoin True  False False = Refl
  proofOfMeetDistributesJoin True  False True  = Refl
  proofOfMeetDistributesJoin True  True  False = Refl
  proofOfMeetDistributesJoin True  True  True  = Refl

public export
BoundedDistributiveLattice Bool where
