module Control.Container

import Builtin

import Data.Bool
import Data.LinkedList
import Relation.Equiv

public export
interface Container c v where
  pack : LinkedList v → c
  unpack : c → LinkedList v
  filter : (v → Bool) → c → c

  proofOfSoundness : (l: c) → (pack ∘ unpack) l = l
  -- The (unpack ∘ pack) l = l might not be true, for example with sets

public export
Container (LinkedList v) v where
  pack   = id
  unpack = id
  filter _   []    = []
  filter f (x::xs) = if f x then x :: (filter f xs) else (filter f xs)

  proofOfSoundness _ = Refl
