module Algebra.Group.Semigroup

import Builtin

import public Algebra.Group.Magma

%default total

public export
interface Magma a ⇒ Semigroup a where
  proofOfAssociativity : (x, y, z: a) → (x ⋄ y) ⋄ z = x ⋄ (y ⋄ z)

public export
interface (CommutativeMagma a, Semigroup a) ⇒ CommutativeSemigroup a where

-- (CommutativeSemigroup a, Semigroup a) ⇒ CommutativeSemigroup a where
