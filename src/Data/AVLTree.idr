module Data.AVLTree

import Builtin

import Algebra.Relation.Equivalence
import Algebra.Relation.Preorder
import Algebra.Relation.Order

import Data.Either
import Data.Natural
import Data.Optional
import Data.PrimInteger

%default total

public export
data AVLTree : (o : Order t) => (t : Type) -> (height : Natural) -> (bounds : Optional (t, t)) -> Type where
  Empty : AVLTree t Zero Nothing {o}
  Node  : AVLTree t leftHeight leftBounds {o}
        -> (pivot : t)
        -> AVLTree t rigthHeight rightBounds {o}
        -> {auto heightCheck : diff leftHeight rightHeight `LTE` 1}
        -- TODO: Figure out how to make Idris2 happy about this signature
        -- -> {auto leftBoundOk  : (optional leftBounds  ((`LT` pivot) . Builtin.snd) Unit)}
        -- -> {auto rightBoundOk : (optional rightBounds ((`GT` pivot) . Builtin.fst) Unit)}
        -> AVLTree t
             (Succesor $ max leftHeight rightHeight)
             (Some (optional leftBounds (Builtin.fst) pivot, optional rightBounds (Builtin.snd) pivot))
             {o}

public export
data NonEmpty : AVLTree t h b {o} -> Type where
  IsNode : NonEmpty (Node _ _ _ @{o})

partial
insert : Order t => AVLTree t h b {o} -> (x : t)
       -> Either
            (AVLTree t           h  (Some (optional b (min x . Builtin.fst) x, optional b (max x . Builtin.snd) x)) {o})
            (AVLTree t (Succesor h) (Some (optional b (min x . Builtin.fst) x, optional b (max x . Builtin.snd) x)) {o})
insert Empty x = Right $ Node Empty x Empty
insert (Node leftTree pivot rightTree {leftHeight} {rightHeight}) x =
  case compare x pivot of
    (Left equiv) => Left $ ?hole1
    (Right (Left  lt)) => ?hole2
    (Right (Right gt)) => ?hole3
