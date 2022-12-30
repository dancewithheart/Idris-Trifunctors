module Data.Verified.Trifunctor

import Data.Trifunctor

%default total

||| Verified Trifunctor
||| A Trifunctor for which identity and composition laws are verified
export
interface Trifunctor t => VerifiedTrifunctor (t : Type -> Type -> Type -> Type) where
  trifunctorIdentity : {a : Type} -> {b : Type} -> {c : Type} ->
                       (x : t a b c) ->
                       timap Basics.id Basics.id Basics.id x = x
  trifunctorComposition : {a : Type} -> {b : Type} -> {c : Type} ->
                          {a1 : Type} -> {b1 : Type} -> {c1 : Type} ->
                          (x : t a b c) ->
                          (fa1 : a -> a1) -> (fb1 : b -> b1) -> (fc1 : c -> c1) ->
                          (fa2 : a1 -> a2) -> (fb2 : b1 -> b2) -> (fc2 : c1 -> c2) ->
                          (timap (fa2 . fa1) (fb2 . fb1) (fc2 . fc1) x) =
                          (timap fa2 fb2 fc2 . timap fa1 fb1 fc1) x
