module Algebra.Ring.Util

import Algebra.Ring.Semiring
import Data.Nat.Basic

public export
pow : (Semiring a) ⇒ a → Nat → a
pow _       Z  = one
pow base (S x) = base ⋅ (pow base x)
