module Data.Nat.PrimCast

import Builtin

import Algebra.Ring.Ring
import Algebra.Ring.Util
import Data.Bool
import Data.Integer
import Data.Nat.Basic
import Data.Nat.Semiring
import Relation.Preorder

%inline
inlineSeveral : Nat → Nat → Nat
inlineSeveral n x = x + ((S $ S $ S $ S $ S $ S $ S $ S $ S $ S Z) `pow` n)

public export
fromInteger : Integer → Nat
fromInteger x =
  if x ≤ 0
    then Z
    else if x ≥ 10000
    then inlineSeveral (S (S (S (S Z)))) $ fromInteger (x - 10000)
    else if x ≥ 1000
    then inlineSeveral (S (S (S Z))) $ fromInteger (x - 1000)
    else if x ≥ 100
    then inlineSeveral (S (S Z)) $ fromInteger (x - 100)
    else if x ≥ 10
    then inlineSeveral (S Z) $ fromInteger (x - 10)
    else S (fromInteger (x - 1))
