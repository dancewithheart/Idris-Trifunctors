module Data.Trifunctor

--import Data.Triple

%default total

||| Trifunctor is abstraction over type with 3 type parameters
||| Progression of abstractions: Functor => Bifunctor => Trifunctor
public export
interface Trifunctor (t : Type -> Type -> Type -> Type) where
  timap : (r -> r2) -> (e -> e2) -> (a -> a2) -> t r e a -> t r2 e2 a2

  bimap : (e -> ee) -> (a -> aa) -> t r e a -> t r ee aa
  bimap = timap id

  map : (a -> aa) -> t r e a -> t r e aa
  map = timap id id

  mapLeft : (e -> ee) -> t r e a -> t r ee a
  mapLeft e = timap id e id

--public export
--implementation Trifunctor Triple where
--  timap f g h cde = _
-- timap f g h cde = MkTriple (f (fst3 cde)) (g (snd3 cde)) (h (trd3 cde))

public export
implementation Trifunctor (\ a => \ b => \ c => (a, b, c)) where
  timap f g h (a, b, c) = (f a, g b, h c)
