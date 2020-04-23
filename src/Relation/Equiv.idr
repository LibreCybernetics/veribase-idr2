module Relation.Equiv

import Builtin
import Data.Bool

%default total

infix 6 ≡, ≢

-- Value Level

public export
interface Equiv a where
  (≡) : a → a → Bool
  (≢) : a → a → Bool
  -- Syntactical Equality (=) is taken as a stronger equality
  -- than Arbitrary Equivalence (≡) but not the other way around!
  proofOfEquality : (x, y: a) → x = y → IsTrue (x ≡ y)
  proofOfSoundness1 : (x, y: a) → IsTrue (x ≡ y) → IsFalse (x ≢ y)
  proofOfSoundness2 : (x, y: a) → IsFalse (x ≢ y) → IsTrue (x ≡ y)
  -- The above gives reflexivity
  proofOfSymetry : (x, y: a) → IsTrue (x ≡ y) → IsTrue (y ≡ x)
  proofOfTransitivity : (x, y, z: a) → IsTrue (x ≡ y)
                      → IsTrue (y ≡ z) → IsTrue (x ≡ z)

-- Type Level
public export
data EQ : Equiv a ⇒ a → a → Type where
  IsEQ : Equiv a ⇒ (x: a) → (y: a) → {auto ok: IsTrue (x ≡ y)} → EQ x y

public export
data NEQ : Equiv a ⇒ a → a → Type where
  IsNEQ : Equiv a ⇒ (x: a) → (y: a ) → {auto ok: IsTrue (x ≢ y)} → NEQ x y

public export
Equiv Bool where
  False ≡ False = True
  True  ≡ True  = True
  _     ≡ _     = False
  False ≢ False = False
  True  ≢ True  = False
  _     ≢ _     = True
  proofOfEquality False False Refl = ItIsTrue
  proofOfEquality False True  Refl impossible
  proofOfEquality True  False Refl impossible
  proofOfEquality True  True  Refl = ItIsTrue
  proofOfSoundness1 False False ItIsTrue = ItIsFalse
  proofOfSoundness1 False True  ItIsTrue impossible
  proofOfSoundness1 True  False ItIsTrue impossible
  proofOfSoundness1 True  True  ItIsTrue = ItIsFalse
  proofOfSoundness2 False False ItIsFalse = ItIsTrue
  proofOfSoundness2 False True  ItIsFalse impossible
  proofOfSoundness2 True  False ItIsFalse impossible
  proofOfSoundness2 True  True  ItIsFalse = ItIsTrue
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
