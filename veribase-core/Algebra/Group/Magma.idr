module Algebra.Group.Magma

import Builtin

infixl 5 ⋄

%default total

public export
interface Magma a where
  (⋄) : a → a → a

public export
interface Magma a ⇒ CommutativeMagma a where
  proofOfCommutativity : (x, y: a) → x ⋄ y = y ⋄ x
