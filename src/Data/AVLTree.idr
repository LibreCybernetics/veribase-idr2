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
        -- -> {auto leftBoundOk  : (optional leftBounds  ((`LT` @{o} pivot) . Builtin.snd) Unit)}
        -- -> {auto rightBoundOk : (optional rightBounds ((`GT` @{o} pivot) . Builtin.fst) Unit)}
        -> AVLTree t
             (Succesor $ max leftHeight rightHeight)
             (Some (optional leftBounds (Builtin.fst) pivot, optional rightBounds (Builtin.snd) pivot))
             {o}

public export
data NonEmpty : AVLTree t h b {o} -> Type where
  IsNode : NonEmpty (Node _ _ _ @{o})

public export
Uninhabited (NonEmpty Empty {o}) where
  uninhabited IsNode impossible

data RotatableLeft : AVLTree t h b {o} -> Type where
  IsRotatableLeft : {leftTree : AVLTree t h1 b1 {o}} -> {rightTree : AVLTree t h2 b2 {o}}
                  -> {auto rightNonEmpty : NonEmpty rightTree}
                  -> {auto heightCheck : diff h1 h2 `LTE` 1}
                  -> RotatableLeft (Node leftTree _ rightTree {heightCheck=ok})

data RotatableRight : AVLTree t h b {o} -> Type where
  IsRotatableRight : {h1, h2 : Natural} -> {leftTree : AVLTree t h1 b1 {o}} -> {rightTree : AVLTree t h2 b2 {o}}
                   -> {auto leftNonEmpty : NonEmpty leftTree}
                   -> {auto heightCheck : diff h1 h2 `LTE` 1}
                   -> RotatableRight (Node leftTree _ rightTree {leftHeight=h1} {rightHeight=h2} {heightCheck=heightCheck})

rotateLeft : (tree : AVLTree t h b {o}) -> {auto ok: RotatableLeft tree} -> AVLTree t h' b' {o}
rotateLeft (Node treeA pivot1 Empty) {ok} = case ok of
  IsRotatableLeft {rightNonEmpty} => absurd rightNonEmpty
rotateLeft (Node treeA pivot1 (Node treeB pivot2 treeC)) {ok} = case ok of
  IsRotatableLeft {heightCheck} => ?holeRotateLeft

rotateRight : (tree : AVLTree t h b {o}) -> {auto ok: RotatableRight tree} -> AVLTree t h' b' {o}
rotateRight (Node Empty pivot2 treeB) {ok} = case ok of
  IsRotatableRight {leftNonEmpty} => absurd leftNonEmpty
rotateRight (Node (Node treeA pivot1 treeB) pivot2 treeC) {ok} = case ok of
  IsRotatableRight {heightCheck} => ?holeRotateRight

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
