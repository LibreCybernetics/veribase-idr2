module Relation.Order

import Builtin

import Data.Bool
import Relation.Preorder

%default total

infix 5 ≤, ≰

public export
interface Preorder a ⇒ PartialOrder a where
  proofOfAntisymetry : (x, y: a) → IsTrue (x ≲ y) → IsTrue (y ≲ x) → x = y

public export
interface (TotalPreorder a, PartialOrder a) ⇒ Order a where

public export
(≤) : PartialOrder a ⇒ a → a → Bool
(≤) = (≲)

public export
(≰) : PartialOrder a ⇒ a → a → Bool
(≰) = (≴)

-- (TotalPreorder a, Order a) ⇒ TotalOrder a where

public export
PartialOrder Bool where
  proofOfAntisymetry False False ItIsTrue ItIsTrue = Refl
  proofOfAntisymetry False True  ItIsTrue ItIsTrue impossible
  proofOfAntisymetry True  False ItIsTrue ItIsTrue impossible
  proofOfAntisymetry True  True  ItIsTrue ItIsTrue = Refl

public export
Order Bool where
