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
  x ≡ y = not (x ≢ y)

  (≢) : a → a → Bool
  x ≢ y = not (x ≡ y)

  proofOfSoundness1 : (x, y: a) → x ≡ y = True → x ≢ y = False
  proofOfSoundness2 : (x, y: a) → x ≢ y = True → x ≡ y = False

  proofOfReflexivity : (x: a) → x ≡ x = True
  proofOfSymetry : (x, y: a) → x ≡ y = True → y ≡ x = True
  proofOfTransitivity : (x, y, z: a) → x ≡ y = True → y ≡ z = True → x ≡ z = True

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

  proofOfSoundness1 False False Refl = Refl
  proofOfSoundness1 False True  Refl impossible
  proofOfSoundness1 True  False Refl impossible
  proofOfSoundness1 True  True  Refl = Refl

  proofOfSoundness2 False False Refl impossible
  proofOfSoundness2 False True  Refl = Refl
  proofOfSoundness2 True  False Refl = Refl
  proofOfSoundness2 True  True  Refl impossible

  proofOfReflexivity False = Refl
  proofOfReflexivity True  = Refl

  proofOfSymetry False False Refl = Refl
  proofOfSymetry False True  Refl impossible
  proofOfSymetry True  False Refl impossible
  proofOfSymetry True  True  Refl = Refl

  proofOfTransitivity False False False Refl Refl = Refl
  proofOfTransitivity False False True  Refl Refl impossible
  proofOfTransitivity False True  _     Refl Refl impossible
  proofOfTransitivity True  False _     Refl Refl impossible
  proofOfTransitivity True  True  False Refl Refl impossible
  proofOfTransitivity True  True  True  Refl Refl = Refl
