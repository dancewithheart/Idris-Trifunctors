module Data.Trifunctor

%access public export

interface Trifunctor (t : Type -> Type -> Type -> Type) where
  timap : (a -> aa) -> (b -> bb) -> (c -> cc) -> t a b c -> t aa bb cc
