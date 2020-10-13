module Data.Verified.Zifunctor

import Data.Zifunctor

%default total
%access public export

||| Verified Zifunctor
||| A Zifunctor for which identity and composition laws are verified
interface Zifunctor t => VerifiedZifunctor (t : Type -> Type -> Type -> Type) where
  zifunctorIdentity : {a : Type} -> {b : Type} -> {c : Type} ->
                     (x : t a b c) ->
                     zimap Basics.id Basics.id Basics.id x = x
  zifunctorComposition : {a : Type} -> {b : Type} -> {c : Type} ->
                         {a1 : Type} -> {b1 : Type} -> {c1 : Type} ->
                         (x : t a b c) ->
                         (fa1 : a1 -> a) -> (fb1 : b -> b1) -> (fc1 : c -> c1) ->
                         (fa2 : a2 -> a1) -> (fb2 : b1 -> b2) -> (fc2 : c1 -> c2) ->
                         (zimap (fa1 . fa2) (fb2 . fb1) (fc2 . fc1) x) =
                         (zimap fa2 fb2 fc2 . zimap fa1 fb1 fc1) x
