module Data.Trifunctor

%access public export

interface Zifunctor (t : Type -> Type -> Type -> Type) where
  zimap : (aa -> a) -> (b -> bb) -> (c -> cc) -> t a b c -> t aa bb cc
