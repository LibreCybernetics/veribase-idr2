module Relation.Equiv

import Builtin

import Algebra.Group.Magma
import Data.Bool

%default total

infix 6 ≡, ≢

--
-- Value Level
--

||| Equiv represents equivalence relations, not equality
||| An `a` might have several equivalence relations
public export
interface Equiv a where
  (≡) : a → a → Bool
  (≢) : a → a → Bool
  proofOfSoundness1 : (x, y: a) → IsTrue (x ≡ y) → IsFalse (x ≢ y)
  proofOfSoundness2 : (x, y: a) → IsFalse (x ≢ y) → IsTrue (x ≡ y)
  proofOfReflexivity : (x: a) → IsTrue (x ≡ x)
  proofOfSymetry : (x, y: a) → IsTrue (x ≡ y) → IsTrue (y ≡ x)
  proofOfTransitivity : (x, y, z: a) → IsTrue (x ≡ y) → IsTrue (y ≡ z) → IsTrue (x ≡ z)

--
-- Type Level
--

public export
data EQ : Equiv a ⇒ a → a → Type where
  IsEQ : Equiv a ⇒ (x, y: a) → {auto ok: IsTrue (x ≡ y)} → EQ x y

public export
data NEQ : Equiv a ⇒ a → a → Type where
  IsNEQ : Equiv a ⇒ (x, y: a) → {auto ok: IsTrue (x ≢ y)} → NEQ x y

--
-- Bool Instance
--

public export
Equiv Bool where
  (≡) = (⋄) @{BoolEquivMagma}
  (≢) = (⋄) @{BoolXorMagma}

  proofOfSoundness1 False False ItIsTrue = ItIsFalse
  proofOfSoundness1 False True  ItIsTrue impossible
  proofOfSoundness1 True  False ItIsTrue impossible
  proofOfSoundness1 True  True  ItIsTrue = ItIsFalse

  proofOfSoundness2 False False ItIsFalse = ItIsTrue
  proofOfSoundness2 False True  ItIsFalse impossible
  proofOfSoundness2 True  False ItIsFalse impossible
  proofOfSoundness2 True  True  ItIsFalse = ItIsTrue

  proofOfReflexivity False = ItIsTrue
  proofOfReflexivity True  = ItIsTrue

  proofOfSymetry False False ItIsTrue = ItIsTrue
  proofOfSymetry False True  ItIsTrue impossible
  proofOfSymetry True  False ItIsTrue impossible
  proofOfSymetry True  True  ItIsTrue = ItIsTrue

  proofOfTransitivity False False False ItIsTrue ItIsTrue = ItIsTrue
  proofOfTransitivity False False True  ItIsTrue ItIsTrue impossible
  proofOfTransitivity False True  _     ItIsTrue ItIsTrue impossible
  proofOfTransitivity True  False _     ItIsTrue ItIsTrue impossible
  proofOfTransitivity True  True  False ItIsTrue ItIsTrue impossible
  proofOfTransitivity True  True  True  ItIsTrue ItIsTrue = ItIsTrue
