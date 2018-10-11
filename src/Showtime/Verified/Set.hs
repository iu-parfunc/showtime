{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
module Showtime.Verified.Set where

import Data.Singletons.Prelude hiding (Map)
import Data.Singletons.TH
import Showtime.Verified.Map

$(singletons [d|
  newtype Set a = MkSet (Map a ())
  |])

$(singletons [d|
  setInsert :: Eq a => a -> Set a -> Set a
  setInsert a (MkSet m) = MkSet (mapInsert a () m)

  setUnion :: Eq a => Set a -> Set a -> Set a
  setUnion (MkSet m1) (MkSet m2) = MkSet (mapUnion m1 m2)
  |])
