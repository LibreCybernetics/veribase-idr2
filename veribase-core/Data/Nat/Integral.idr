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

%builtinNatSub minus
%builtinNatDiv div
%builtinNatMod mod

-- limited minus
public export
minus : (x, y: Nat) → Nat
minus    x     Z  = x
minus    Z  (S _) = Z
minus (S x) (S y) = x `minus` y

div : Nat → Nat → Nat
div _      Z  = Z
div Z      _  = Z
div n d@(S _) with (n ≥ d)
  div n d@(S _) | False = Z
  div n d@(S _) | True  = S $ (n `minus` d) `div` d

mod : Nat → Nat → Nat
mod _      Z  = Z
mod Z      _  = Z
mod n d@(S _) with (n ≥ d)
  mod n d@(S _) | False = n
  mod n d@(S _) | True  = (n `minus` d) `mod` d

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
  divMod n d       = (n `div` d, n `mod` d)
