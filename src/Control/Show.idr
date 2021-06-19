module Control.Show

%default total

public export
interface Show t where
  show : t -> String
