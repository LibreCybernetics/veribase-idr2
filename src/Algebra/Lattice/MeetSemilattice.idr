module Algebra.Lattice.MeetSemilattice

import public Builtin

import public Algebra.Relation.Order

%default total

infixl 5 /\

public export
interface Order t => MeetSemilattice t where
  (/\) : t -> t -> t

  proofIdempotence : (x : t) -> x /\ x = x
  proofCommutative : (x, y : t) -> x /\ y = y /\ x
  proofAssociative : (x, y, z : t) -> x /\ (y /\ z) = (x /\ y) /\ z

  proofLowerBound : (x, y : t) -> (x /\ y `LTE` x, x /\ y `LTE` y)
  proofGreatestLowerBound : (b, x, y : t) -> b `LTE` x -> b `LTE` y -> b `LTE` x /\ y
