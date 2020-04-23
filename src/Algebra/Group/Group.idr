module Algebra.Group.Group

import Builtin

import public Algebra.Group.Monoid

%default total

public export
interface (Magma a, Semigroup a, Monoid a) ⇒ Group a where
  inv : a → a
  proofOfLeftInverse  : (x : a) → (inv x) ⋄ x = Monoid.e
  proofOfRightInverse : (x : a) → x ⋄ (inv x) = Monoid.e

public export
interface (CommutativeMagma a, Group a) ⇒ CommutativeGroup a where

-- (CommutativeMagma a, Group a) ⇒ CommutativeGroup a where
