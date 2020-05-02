module Data.ListComprehension

import Data.Bool
import Data.Container
import Data.Nat.Order
import Data.LinkedList
import Relation.Order

public export
interface (Order v, Container c v) ⇒ ListComprehension c v where
  rangeFromTo : v → v → c

public export
ListComprehension (LinkedList Nat) Nat where
  rangeFromTo x y = if x ≤ y then x :: (rangeFromTo (S x) y) else []
