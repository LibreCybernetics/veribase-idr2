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
data AVLTree : (t : Type) -> (o : Order t) => (height : Natural) -> (bounds : Optional (t, t)) -> Type where
  Empty : AVLTree t Zero Nothing {o}
  Node  : {leftHeight, rightHeight : Natural} -> {leftBounds, rightBounds : Optional (t, t)}
        -> AVLTree t leftHeight leftBounds {o}
        -> (pivot : t)
        -> AVLTree t rigthHeight rightBounds {o}
        -> {auto heightOk : diff leftHeight rightHeight `LTE` 1}
        -> {auto leftBoundOk  : (optional leftBounds  ((\b => LT @{o} b pivot) . Builtin.snd) Unit)}
        -> {auto rightBoundOk : (optional rightBounds ((\b => GT @{o} b pivot) . Builtin.fst) Unit)}
        -> AVLTree t
             (Succesor $ max leftHeight rightHeight)
             (Some (optional leftBounds (Builtin.fst) pivot, optional rightBounds (Builtin.snd) pivot))
             {o}

public export
data NonEmpty : AVLTree t h b {o} -> Type where
  IsNode : {leftHeight, rightHeight : Natural}
         -> {leftTree : AVLTree t leftHeight leftBounds {o}}
         -> {pivot : t}
         -> {rightTree : AVLTree t rightHeight rightBounds {o}}
         -> {auto leftBound : (optional leftBounds  ((\b => LT @{o} b pivot) . Builtin.snd) Unit)}
         -> {auto rightBound : (optional rightBounds ((\b => GT @{o} b pivot) . Builtin.fst) Unit)}
         -> {auto height : diff leftHeight rightHeight `LTE` 1}
         -> NonEmpty (Node leftTree pivot rightTree {leftHeight=leftHeight} {rightHeight=rightHeight})

public export
Uninhabited (NonEmpty Empty {o}) where
  uninhabited IsNode impossible

data RotatableLeft : AVLTree t h b {o} -> Type where
  IsRotatableLeft : {leftHeight, rightHeight : Natural}
                  -> {leftTree : AVLTree t leftHeight leftBounds {o}}
                  -> {pivot : t}
                  -> {rightTree : AVLTree t rightHeight rightBounds {o}}
                  -> {auto rightNonEmpty : NonEmpty rightTree}
                  -> {auto balanceFactor : leftHeight `LT` rightHeight}
                  -> {auto leftBound : (optional leftBounds  ((\b => LT @{o} b pivot) . Builtin.snd) Unit)}
                  -> {auto rightBound : (optional rightBounds ((\b => GT @{o} b pivot) . Builtin.fst) Unit)}
                  -> {auto height : diff leftHeight rightHeight `LTE` 1}
                  -> RotatableLeft (Node leftTree pivot rightTree {leftHeight=leftHeight} {rightHeight=rightHeight})

data RotatableRight : AVLTree t h b {o} -> Type where
  IsRotatableRight : {leftHeight, rightHeight : Natural}
                   -> {leftTree : AVLTree t leftHeight leftBounds {o}}
                   -> {pivot : t}
                   -> {rightTree : AVLTree t rightHeight rightBounds {o}}
                   -> {auto leftNonEmpty : NonEmpty leftTree}
                   -> {auto balanceFactor : rightHeight `LT` leftHeight}
                   -> {auto leftBound : (optional leftBounds  ((\b => LT @{o} b pivot) . Builtin.snd) Unit)}
                   -> {auto rightBound : (optional rightBounds ((\b => GT @{o} b pivot) . Builtin.fst) Unit)}
                   -> {auto height : diff leftHeight rightHeight `LTE` 1}
                   -> RotatableRight (Node leftTree pivot rightTree {leftHeight=leftHeight} {rightHeight=rightHeight})

rotateLeft : (tree : AVLTree t h b {o}) -> {auto ok: RotatableLeft tree} -> AVLTree t ?holeHeight (Some ?holeBounds) {o}
rotateLeft (Node treeA pivot1 Empty) {ok} = case ok of
  IsRotatableLeft {rightNonEmpty} => absurd rightNonEmpty
rotateLeft (Node treeA pivot1 (Node treeB pivot2 treeC)) {ok} = case ok of
  IsRotatableLeft {balanceFactor=ZeroLTEAny} impossible
  IsRotatableLeft {leftHeight} {rightHeight=Succesor (max rightLeftHeight rightRightHeight)} {balanceFactor=SuccesorLTE p} =>
    ?holeRotateLeft -- Node (Node treeA pivot1 treeB) pivot2 treeC -- rewrite proofDiffGTEThenMinus rightHeight leftHeight balanceFactor in ?holeRotateLeft

rotateRight : (tree : AVLTree t h b {o}) -> {auto ok: RotatableRight tree} -> AVLTree t h' b' {o}
rotateRight (Node Empty pivot2 treeB) {ok} = case ok of
  IsRotatableRight {leftNonEmpty} => absurd leftNonEmpty
rotateRight (Node (Node treeA pivot1 treeB) pivot2 treeC) {ok} = case ok of
  IsRotatableRight {height} => ?holeRotateRight
