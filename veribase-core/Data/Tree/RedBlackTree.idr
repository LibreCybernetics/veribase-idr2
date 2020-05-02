module Data.Tree.RedBlackTree

mutual
  public export
  data RedBlackTree : (v : Type) -> Type where
    Leaf      : v -> RedBlackTree v
    BlackNode : RedBlackTree v -> RedBlackTree v -> RedBlackTree v
    RedNode   : (t1: RedBlackTree v) -> {auto ok1: IsBlack t1}
              -> (t2: RedBlackTree v) -> {auto ok2: IsBlack t2}
              -> RedBlackTree v

  public export
  data IsBlack : RedBlackTree v -> Type where
    LeafIsBlack      : IsBlack (Leaf _)
    BlackNodeIsBlack : IsBlack (BlackNode _ _)
