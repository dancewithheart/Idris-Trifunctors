module Data.Fufunctor

import Data.Morphisms

%default total
%access public export

-- FuFunctor is dual to Zivunctor
-- More precisely dual would be t c b a, but in current form
-- it is already used in ZIO library and (Schedule)
-- also it match the Function2 shape a -> b -> c

-- Since it is not exact dual the name is not CoZifunctor but Function2 Functor
-- or FuFunctor in short
interface Fufunctor (t : Type -> Type -> Type -> Type) where
  fumap : (rr -> r) -> (ee -> e) -> (a -> aa) -> t r e a -> t rr ee aa

  dimap : (rr -> r) -> (a -> aa) -> t r e a -> t rr e aa
  dimap r = fumap r id

  dimapRight : (ee -> e) -> (a -> aa) -> t r e a -> t r ee aa
  dimapRight e a = fumap id e a

  map : (a -> aa) -> t r e a -> t r e aa
  map = fumap id id

  contramap : (rr -> r) -> t r e a -> t rr e a
  contramap r = fumap r id id

-- implementation Fufunctor Trimorphism where
--  fumap f g h (Trimo fa) = Trimo ( \ee -> \aa -> h (fa (f ee) (g aa)) )
