module Verilude

import public Data.Bool
import public Relation.Equiv
import public Relation.Preorder
import public Relation.Order

isEqual : (x: Bool) -> (y: Bool) -> {auto ok: x `EQ` y} -> Bool
isEqual _ _ = True
