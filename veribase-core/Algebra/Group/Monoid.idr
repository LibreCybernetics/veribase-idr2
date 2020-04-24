module Algebra.Group.Monoid

import Builtin

import public Algebra.Group.Semigroup

%default total

public export
interface (Magma a, Semigroup a) ⇒ Monoid a where
  e : a
  proofOfLeftIdentity  : (x : a) → e ⋄ x = x
  proofOfRightIdentity : (x : a) → x ⋄ e = x

public export
interface (CommutativeMagma a, Monoid a) ⇒ CommutativeMonoid a where

-- (CommutativeMagma a, Monoid a) ⇒ CommutativeMonoid a where
