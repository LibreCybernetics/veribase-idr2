module Data.Maybe

import Builtin

import Algebra.Group.Monoid

%default total

public export
data Maybe a = Nothing | Some a

public export
(Magma a) ⇒ Magma (Maybe a) where
  Nothing  ⋄ Nothing  = Nothing
  Nothing  ⋄ (Some y) = Some y
  (Some x) ⋄ Nothing  = Some x
  (Some x) ⋄ (Some y) = Some (x ⋄ y)

public export
(CommutativeMagma a) ⇒ CommutativeMagma (Maybe a) where
  proofOfCommutativity Nothing  Nothing  = Refl
  proofOfCommutativity Nothing  (Some y) = Refl
  proofOfCommutativity (Some x) Nothing  = Refl
  proofOfCommutativity (Some x) (Some y) = rewrite proofOfCommutativity x y in Refl

public export
(Semigroup a) ⇒ Semigroup (Maybe a) where
  proofOfAssociativity Nothing  Nothing  Nothing  = Refl
  proofOfAssociativity Nothing  Nothing  (Some z) = Refl
  proofOfAssociativity Nothing  (Some y) Nothing  = Refl
  proofOfAssociativity Nothing  (Some y) (Some z) = Refl
  proofOfAssociativity (Some x) Nothing  Nothing  = Refl
  proofOfAssociativity (Some x) Nothing  (Some z) = Refl
  proofOfAssociativity (Some x) (Some y) Nothing  = Refl
  proofOfAssociativity (Some x) (Some y) (Some z) = rewrite proofOfAssociativity x y z in Refl

public export
(Semigroup (Maybe a)) ⇒ Monoid (Maybe a) where
  e = Nothing

  -- TODO: Create Minimum Reproducible example of Elab not normalizing with `e`
  -- proofOfLeftIdentity Nothing  = Refl
  -- proofOfLeftIdentity (Some x) = Refl

  -- proofOfRightIdentity Nothing  = Refl
  -- proofOfRightIdentity (Some x) = Refl
