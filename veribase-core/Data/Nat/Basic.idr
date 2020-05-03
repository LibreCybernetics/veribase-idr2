module Data.Nat.Basic

%default total

%builtinNatZero Z
%builtinNatSucc S

public export
data Nat = Z | S Nat
