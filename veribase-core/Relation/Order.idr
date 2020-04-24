module Relation.Order

import Builtin

import Data.Bool
import Relation.Equiv
import Relation.Preorder

%default total

infix 5 ≤, ≥, <, >, ≮, ≯, ≰, ≱

--
-- Value Level
--

||| An order might not be total (Both x ≲ y and x ≳ y might be false) and
||| an order antisymetry only implies Equivalence (If you need equality use StrictOrder)
public export
interface (Equiv a, Preorder a) ⇒ Order a where
  (<) : a → a → Bool
  (≮) : a → a → Bool
  proofOfAntisymetry : (x, y: a) → IsTrue (x ≲ y) → IsTrue (y ≲ x) → x `EQ` y
  proofOfSoundness1 : (x, y: a) → IsTrue (x < y) → IsTrue (x ≲ y)
  proofOfSoundness2 : (x, y: a) → IsTrue (x < y) → x `NEQ` y
  proofOfSoundness3 : (x, y: a) → IsTrue (x < y) → IsFalse (x ≮ y)
  proofOfSoundness4 : (x, y: a) → IsTrue (x ≮ y) → IsFalse (x < y)

-- Constrainted Aliases for Preorders

public export
(≤) : Order a ⇒ a → a → Bool
(≤) = (≲)

public export
(≰) : Order a ⇒ a → a → Bool
(≰) = (≴)

public export
(≥) : Order a ⇒ a → a → Bool
(≥) = flip (≲)

public export
(≱) : Order a ⇒ a → a → Bool
(≱) = flip (≴)

public export
(>) : Order a ⇒ a → a → Bool
(>) = flip (<)

public export
(≯) : Order a ⇒ a → a → Bool
(≯) = flip (≮)

-- Stronger Orders

||| A StrictOrder might not be total (Both x ≲ y and x ≳ y might be false)
public export
interface Order a => StrictOrder a where
  proofOfStrictAntisymetry : (x, y: a) → IsTrue (x ≲ y) → IsTrue (y ≲ x) → x = y

public export
interface (TotalPreorder a, Order a) ⇒ TotalOrder a where

public export
interface (StrictOrder a, TotalOrder a) ⇒ StrictTotalOrder a where

-- TODO: Uncomment when Idris!306 (https://github.com/edwinb/Idris2/issues/306) gets resolved
-- (TotalPreorder a, PartialOrder a) ⇒ TotalOrder a where
-- (StrictPartialOrder a, TotalOrder a) ⇒ StrictTotalOrder a where

--
-- Type Level
--

public export
data LTE : Order a ⇒ a → a → Type where
  IsLTE : Order a ⇒ (x, y: a) → {auto ok: IsTrue (x ≤ y)} → LTE x y

public export
data GTE : Order a ⇒ a → a → Type where
  IsGTE : Order a ⇒ (x, y: a) → {auto ok: IsTrue (x ≥ y)} → GTE x y

public export
data LT : Order a ⇒ a → a → Type where
  IsLT : Order a ⇒ (x, y: a) → {auto ok: IsTrue (x < y)} → LT x y

public export
data GT : Order a ⇒ a → a → Type where
  IsGT : Order a ⇒ (x, y: a) → {auto ok: IsTrue (x > y)} → GT x y

--
-- Bool Implementation
--

public export
Order Bool where
  False < True = True
  _     < _    = False

  False ≮ True = False
  _     ≮ _    = True

  proofOfAntisymetry False False ItIsTrue ItIsTrue = IsEQ False False
  proofOfAntisymetry False True  ItIsTrue ItIsTrue impossible
  proofOfAntisymetry True  False ItIsTrue ItIsTrue impossible
  proofOfAntisymetry True  True  ItIsTrue ItIsTrue = IsEQ True  True

  proofOfSoundness1 False False ItIsTrue impossible
  proofOfSoundness1 False True  ItIsTrue = ItIsTrue
  proofOfSoundness1 True  False ItIsTrue impossible
  proofOfSoundness1 True  True  ItIsTrue impossible

  proofOfSoundness2 False False ItIsTrue impossible
  proofOfSoundness2 False True  ItIsTrue = IsNEQ False True
  proofOfSoundness2 True  False ItIsTrue impossible
  proofOfSoundness2 True  True  ItIsTrue impossible

  proofOfSoundness3 False False ItIsTrue impossible
  proofOfSoundness3 False True  ItIsTrue = ItIsFalse
  proofOfSoundness3 True  False ItIsTrue impossible
  proofOfSoundness3 True  True  ItIsTrue impossible

  proofOfSoundness4 False False ItIsTrue = ItIsFalse
  proofOfSoundness4 False True  ItIsTrue impossible
  proofOfSoundness4 True  False ItIsTrue = ItIsFalse
  proofOfSoundness4 True  True  ItIsTrue = ItIsFalse

public export
StrictOrder Bool where
  proofOfStrictAntisymetry False False ItIsTrue ItIsTrue = Refl
  proofOfStrictAntisymetry False True  ItIsTrue ItIsTrue impossible
  proofOfStrictAntisymetry True  False ItIsTrue ItIsTrue impossible
  proofOfStrictAntisymetry True  True  ItIsTrue ItIsTrue = Refl
