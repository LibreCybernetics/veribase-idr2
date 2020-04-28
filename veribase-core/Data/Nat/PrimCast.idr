module Data.Nat.PrimCast

import Builtin

import Algebra.Ring.Ring
import Data.Bool
import Data.Integer
import Data.Nat.Basic
import Relation.Preorder

public export
fromInteger : Integer → Nat
fromInteger x =
  if x ≤ 0
    then Z
    else S (fromInteger (x - 1))
