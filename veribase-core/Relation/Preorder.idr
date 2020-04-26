module Relation.Preorder

import Builtin

import Algebra.Group.Magma
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
  x ≲ y = not (x ≴ y)
  (≴) : a → a → Bool
  x ≴ y = not (x ≲ y)
  proofOfSoundness1 : (x, y: a) → x ≲ y = True → x ≴ y = False
  proofOfSoundness2 : (x, y: a) → x ≴ y = True → x ≲ y = False
  proofOfReflexivity : (x: a) → x ≲ x = True
  proofOfTransitivity : (x, y, z: a) → x ≲ y = True → y ≲ z = True → x ≲ z = True

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
  proofOfTotality : (x, y: a) → Either (x ≲ y = True) (x ≳ y = True)

--
-- Bool Instance
--

public export
Preorder Bool where
  (≲) = (⋄) @{BoolImplMagma}

  True ≴ False = True
  _    ≴ _     = False

  proofOfSoundness1 False False Refl = Refl
  proofOfSoundness1 False True  Refl = Refl
  proofOfSoundness1 True  False Refl impossible
  proofOfSoundness1 True  True  Refl = Refl

  proofOfSoundness2 False False Refl impossible
  proofOfSoundness2 False True  Refl impossible
  proofOfSoundness2 True  False Refl = Refl
  proofOfSoundness2 True  True  Refl impossible

  proofOfReflexivity False = Refl
  proofOfReflexivity True  = Refl

  proofOfTransitivity False False False Refl Refl = Refl
  proofOfTransitivity False False True  Refl Refl = Refl
  proofOfTransitivity False True  False Refl Refl impossible
  proofOfTransitivity False True  True  Refl Refl = Refl
  proofOfTransitivity True  False False Refl Refl impossible
  proofOfTransitivity True  False True  Refl Refl impossible
  proofOfTransitivity True  True  False Refl Refl impossible
  proofOfTransitivity True  True  True  Refl Refl = Refl

public export
TotalPreorder Bool where
  proofOfTotality False False = Left  Refl
  proofOfTotality False True  = Left  Refl
  proofOfTotality True  False = Right Refl
  proofOfTotality True  True  = Right Refl
