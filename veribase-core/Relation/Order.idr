module Relation.Order

import Builtin

import Data.Bool
import Relation.Equiv
import public Relation.Preorder

%default total

infix 5 <, >, ≮, ≯

--
-- Value Level
--

||| An order might not be total (Both x ≲ y and x ≳ y might be false) and
||| an order antisymetry only implies Equivalence (If you need equality use StrictOrder)
public export
interface (Equiv a, Preorder a) ⇒ Order a where
  (<) : a → a → Bool
  (≮) : a → a → Bool
  proofOfAntisymetry : (x, y: a) → x ≤ y = True → x ≤ y = True → x `EQ` y
  proofOfSoundness1 : (x, y: a) → x < y = True → x ≤ y = True
  proofOfSoundness2 : (x, y: a) → x < y = True → x `NEQ` y
  proofOfSoundness3 : (x, y: a) → x < y = True → x ≮ y = False
  proofOfSoundness4 : (x, y: a) → x ≮ y = True → x < y = False

-- Flipped versions

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
  proofOfStrictAntisymetry : (x, y: a) → x ≤ y = True → y ≤ x = True → x = y

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
  IsLTE : Order a ⇒ (x, y: a) → {auto ok: x ≤ y = True} → LTE x y

public export
data GTE : Order a ⇒ a → a → Type where
  IsGTE : Order a ⇒ (x, y: a) → {auto ok: x ≥ y = True} → GTE x y

public export
data LT : Order a ⇒ a → a → Type where
  IsLT : Order a ⇒ (x, y: a) → {auto ok: x < y = True} → LT x y

public export
data GT : Order a ⇒ a → a → Type where
  IsGT : Order a ⇒ (x, y: a) → {auto ok: x > y = True} → GT x y

--
-- Bool Implementation
--

public export
Order Bool where
  False < True = True
  _     < _    = False

  False ≮ True = False
  _     ≮ _    = True

  proofOfAntisymetry False False Refl Refl = IsEQ False False
  -- proofOfAntisymetry False True  Refl Refl impossible
  -- proofOfAntisymetry True  False Refl Refl impossible
  proofOfAntisymetry True  True  Refl Refl = IsEQ True  True

  proofOfSoundness1 False False Refl impossible
  proofOfSoundness1 False True  Refl = Refl
  proofOfSoundness1 True  False Refl impossible
  proofOfSoundness1 True  True  Refl impossible

  proofOfSoundness2 False False Refl impossible
  proofOfSoundness2 False True  Refl = IsNEQ False True
  proofOfSoundness2 True  False Refl impossible
  proofOfSoundness2 True  True  Refl impossible

  proofOfSoundness3 False False Refl impossible
  proofOfSoundness3 False True  Refl = Refl
  proofOfSoundness3 True  False Refl impossible
  proofOfSoundness3 True  True  Refl impossible

  proofOfSoundness4 False False Refl = Refl
  proofOfSoundness4 False True  Refl impossible
  proofOfSoundness4 True  False Refl = Refl
  proofOfSoundness4 True  True  Refl = Refl

public export
StrictOrder Bool where
  proofOfStrictAntisymetry False False Refl Refl = Refl
  proofOfStrictAntisymetry False True  Refl Refl impossible
  proofOfStrictAntisymetry True  False Refl Refl impossible
  proofOfStrictAntisymetry True  True  Refl Refl = Refl
