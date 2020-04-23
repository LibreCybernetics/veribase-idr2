module Algebra.Group.Quasigroup

import Builtin

import public Algebra.Group.Magma

%default total

public export
interface Magma a ⇒ Quasigroup a where
  proofOfLeftCancellative  : (x, y, z : a) → x ⋄ y = x ⋄ z → y = z
  proofOfRightCancellative : (x, y, z : a) → y ⋄ x = z ⋄ x → y = z
