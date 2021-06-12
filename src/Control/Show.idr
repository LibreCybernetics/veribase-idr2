module Control.Show

public export
interface Show t where
  show : t -> String
