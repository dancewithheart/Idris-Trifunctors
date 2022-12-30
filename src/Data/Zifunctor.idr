module Data.Trifunctor

%default total

||| Zifunctor is abstraction over description of computation t that:
||| takes r as input (reader, input)
||| produce result a (a result)
||| or produce error of type e
||| Progression of abstractions: Functor => Bifunctor, Profunctor => Zifunctor
||| Zifunctor combine capabilities of Functor, Bifunctor, Profunctor and add more
interface Zifunctor (t : Type -> Type -> Type -> Type) where
  zimap : (rr -> r) -> (e -> ee) -> (a -> aa) -> t r e a -> t rr ee aa

  bimap : (e -> ee) -> (a -> aa) -> t r e a -> t r ee aa
  bimap = zimap id

  dimap : (rr -> r) -> (a -> aa) -> t r e a -> t rr e aa
  dimap r = zimap r id

  dimapLeft : (rr -> r) -> (e -> ee) -> t r e a -> t rr ee a
  dimapLeft r e = zimap r e id

  map : (a -> aa) -> t r e a -> t r e aa
  map = zimap id id

  mapLeft : (e -> ee) -> t r e a -> t r ee a
  mapLeft e = zimap id e id

  contramap : (rr -> r) -> t r e a -> t rr e a
  contramap r = zimap r id id

-- TODO Zifunctor implementation for r -> Either e a
-- TODO Zifunctor implementation for r -> (e,a)
-- TODO Zifunctor implementation for Bifunctor b => r -> b e a
