module Data.Trifunctor

%default total
%access public export

||| Trifunctor is abstraction over type with 3 type parameters
||| Progression of abstractions: Functor => Bifunctor => Trifunctor
interface Trifunctor (t : Type -> Type -> Type -> Type) where
  timap : (r -> rr) -> (e -> ee) -> (a -> aa) -> t r e a -> t rr ee aa

  bimap : (e -> ee) -> (a -> aa) -> t r e a -> t r ee aa
  bimap = timap id

  map : (a -> aa) -> t r e a -> t r e aa
  map = timap id id

  mapLeft : (e -> ee) -> t r e a -> t r ee a
  mapLeft e = timap id e id
