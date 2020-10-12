module Data.Trifunctor

%default total
%access public export

||| Trifunctor is abstraction over description of computation t that:
||| takes r as input (reader, input)
||| produce result a (a result)
||| or produce error of type e
interface Trifunctor (t : Type -> Type -> Type -> Type) where
  timap : (r -> rr) -> (e -> ee) -> (a -> aa) -> t r e a -> t rr ee aa

  bimap : (e -> ee) -> (a -> aa) -> t r e a -> t r ee aa
  bimap = timap id

  map : (a -> aa) -> t r e a -> t r e aa
  map = timap id id

  mapLeft : (e -> ee) -> t r e a -> t r ee a
  mapLeft e = timap id e id
