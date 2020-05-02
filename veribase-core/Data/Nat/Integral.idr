module Data.Nat.Integral

import Builtin

import Algebra.Ring.Ring
import Algebra.Ring.Util
import Data.Bool
import Data.Integer
import Data.Integral
import Data.Nat.Basic
import Data.Nat.Order
import Data.Nat.Semiring
import Relation.Order

%inline
inlineSeveral : Nat → Nat → Nat
inlineSeveral n x = x + ((S $ S $ S $ S $ S $ S $ S $ S $ S $ S Z) `pow` n)


-- limited minus
public export
minus : (x, y: Nat) → Nat
minus    x     Z  = x
minus    Z  (S _) = Z
minus (S x) (S y) = x `minus` y

public export
Integral Nat where
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
  divMod _ Z       = (Z, Z)
  divMod n d@(S _) with (n ≥ d)
    divMod n d@(S _) | False = (Z, n)
    divMod n d@(S _) | True  = case divMod (n `minus` d) d of
                                    (n', m) ⇒ (S n', m)
