module Data.Natural.Show

import Builtin

import Control.Show

import Data.PrimInteger

import public Data.Natural.SupportPrimIntegerLiteral

%default total

public export
Show Natural where
  show = show . toPrimInteger
