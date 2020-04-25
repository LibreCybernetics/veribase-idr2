module Algebra.Group.Loop

import Builtin

import public Algebra.Group.Quasigroup

%default total

public export
interface Quasigroup a ⇒ Loop a where
  e : a
  proofOfLeftIdentity  : (x: a) → e ⋄ x = x
  proofOfRightIdentity : (x: a) → x ⋄ e = x

public export
interface (CommutativeQuasigroup a, Loop a) ⇒ CommutativeLoop where

-- TODO: Uncomment when Idris!306 (https://github.com/edwinb/Idris2/issues/306) gets resolved
-- (CommutativeQuasigroup a, Loop a) ⇒ CommutativeLoop where
