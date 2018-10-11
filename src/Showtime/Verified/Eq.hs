{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
module Showtime.Verified.Eq where

import Data.Singletons.Prelude
import Showtime.Verified.So

class (Eq a, PEq a, SEq a) => VEq a where
  eqReflexive :: forall (x :: a).
                 Sing x -> So (x == x)
  eqSymmetric :: forall (x :: a) (y :: a).
                 Sing x -> Sing y
              -> So (x == y) -> So (y == x)
  eqTransitive :: forall (x :: a) (y :: a) (z :: a).
                  Sing x -> Sing y -> Sing z
               -> So (x == y) -> So (y == z) -> So (x == z)
