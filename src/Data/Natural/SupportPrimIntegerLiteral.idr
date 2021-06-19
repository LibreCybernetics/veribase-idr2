module Data.Natural.SupportPrimIntegerLiteral

import Builtin

import Algebra.Relation.Preorder

import Data.PrimInteger

import public Data.Natural.Basic

%default total

public export
natFromPrimInteger : (x : Integer) -> {auto ok : x `GTE` 0} -> Natural
natFromPrimInteger 0 = Zero
natFromPrimInteger x = case (decGTE (prim__sub_Integer x 1) 0) of
  Yes p => Succesor $ assert_total $ natFromPrimInteger $ prim__sub_Integer x 1
  No cp => void $ believe_me () -- TODO: impossible

-- TODO: Compiler not happy
-- %builtin IntegerToNatural natFromPrimInteger

public export
natToPrimInteger : Natural -> Integer
natToPrimInteger Zero = 0
natToPrimInteger (Succesor x) = prim__add_Integer 1 $ natToPrimInteger x

-- TODO: Compiler not happy
-- %builtin NaturalToInteger natToPrimInteger

public export
SupportPrimIntegerLiteral Natural where
  PrimIntegerRestriction x = x `GTE` 0
  fromPrimInteger = natFromPrimInteger
  toPrimInteger   = natToPrimInteger
