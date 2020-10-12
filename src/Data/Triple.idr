module Triple

%default total
%access public export
%language LinearTypes

data Triple : (A : Type) -> (B : Type) -> (C : Type) -> Type where
  MkTriple : {A, B, C : Type} ->
             (1 a : A) -> ( 1 b : B) -> (1 c : C) ->
             Triple A B C

-- TODO add dependent triple
-- based on https://github.com/idris-lang/Idris-dev/blob/master/libs/prelude/Builtins.idr

fst3 : (a,b,c) -> a
fst3 (x, y, z) = x

snd3 : (a,b,c) -> b
snd3 (x, y, z) = y

trd3 : (a,b,c) -> c
trd3 (x, y, z) = z

-- TODO add flip12 swap23 etc
-- based on https://github.com/idris-lang/Idris-dev/blob/master/libs/prelude/Prelude/Basics.idr

-- TODO implementation Trifunctor Triple
