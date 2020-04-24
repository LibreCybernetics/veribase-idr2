module Relation.Preorder

import Builtin

import Data.Bool
import Data.Either

%default total

infix 5 ≲, ≴, ≳, ≵

--
-- Value Level
--

||| A preorder might not be total (Both x ≲ y and x ≳ y might be false) and
||| a preorder might not be antisymetric (Even if x ≲ y and x ≳ are true, x ≡ y might be false)
public export
interface Preorder a where
  (≲) : a → a → Bool
  (≴) : a → a → Bool
  proofOfSoundness1 : (x, y: a) → IsTrue (x ≲ y) → IsFalse (x ≴ y)
  proofOfSoundness2 : (x, y: a) → IsTrue (x ≴ y) → IsFalse (x ≲ y)
  proofOfReflexivity : (x: a) → IsTrue (x ≲ x)
  proofOfTransitivity : (x, y, z: a) → IsTrue (x ≲ y) → IsTrue (y ≲ z) → IsTrue (x ≲ z)

-- Fliped versions

public export
(≳) : Preorder a ⇒ a → a → Bool
(≳) = flip (≲)

public export
(≵) : Preorder a ⇒ a → a → Bool
(≵) = flip (≴)

||| Unlike Preorder, TotalPreorder guarantees that either x ≲ y or x ≳ y
public export
interface Preorder a ⇒ TotalPreorder a where
  proofOfTotality : (x, y: a) → Either (IsTrue (x ≲ y)) (IsTrue (x ≳ y))

--
-- Bool Instance
--

public export
Preorder Bool where
  True ≲ False = False
  True ≲ True  = True
  _    ≲ _     = True

  True ≴ False = True
  True ≴ True  = False
  _    ≴ _     = False

  proofOfSoundness1 False False ItIsTrue = ItIsFalse
  proofOfSoundness1 False True  ItIsTrue = ItIsFalse
  proofOfSoundness1 True  False ItIsTrue impossible
  proofOfSoundness1 True  True  ItIsTrue = ItIsFalse

  proofOfSoundness2 False False ItIsTrue impossible
  proofOfSoundness2 False True  ItIsTrue impossible
  proofOfSoundness2 True  False ItIsTrue = ItIsFalse
  proofOfSoundness2 True  True  ItIsTrue impossible

  proofOfReflexivity False = ItIsTrue
  proofOfReflexivity True  = ItIsTrue

  proofOfTransitivity False False False ItIsTrue ItIsTrue = ItIsTrue
  proofOfTransitivity False False True  ItIsTrue ItIsTrue = ItIsTrue
  proofOfTransitivity False True  False ItIsTrue ItIsTrue impossible
  proofOfTransitivity False True  True  ItIsTrue ItIsTrue = ItIsTrue
  proofOfTransitivity True  False False ItIsTrue ItIsTrue impossible
  proofOfTransitivity True  False True  ItIsTrue ItIsTrue impossible
  proofOfTransitivity True  True  False ItIsTrue ItIsTrue impossible
  proofOfTransitivity True  True  True  ItIsTrue ItIsTrue = ItIsTrue

public export
TotalPreorder Bool where
  proofOfTotality False False = Left  ItIsTrue
  proofOfTotality False True  = Left  ItIsTrue
  proofOfTotality True  False = Right ItIsTrue
  proofOfTotality True  True  = Right ItIsTrue

--
-- TODO: Either Instances?
--
