module Data.Trimorphisms

%default total

data Trimorphism : Type -> Type -> Type -> Type where
  Trimo : (a -> b -> c) -> Trimorphism a b c

applyTimo : Trimorphism a b c -> a -> b -> c
applyTimo (Trimo t) a b = (t a) b
