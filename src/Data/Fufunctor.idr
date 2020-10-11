module Data.Fufunctor

%access public export

-- FuFunctor is dual to Zivunctor (dual would be t c b a)
interface Fufunctor (t : Type -> Type -> Type -> Type) where
  fumap : (aa -> a) -> (bb -> b) -> (c -> cc) -> t a b c -> t aa bb cc
