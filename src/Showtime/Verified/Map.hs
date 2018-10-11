{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
module Showtime.Verified.Map where

import Algebra.Lattice
import Data.Singletons.Prelude hiding (Map)
import Data.Singletons.TH
import Showtime.Verified.Eq
import Showtime.Verified.Lattice
import Showtime.Verified.So

$(singletons [d|
  newtype Map k v = MkMap { unMap :: [(k, v)] }
  |])

$(singletons [d|
  mapEmpty :: Map k v
  mapEmpty = MkMap []

  mapInsert :: Eq k => k -> v -> Map k v -> Map k v
  mapInsert = mapInsertWith const

  mapInsertWith :: Eq k => (v -> v -> v) -> k -> v -> Map k v -> Map k v
  mapInsertWith _ new_k new_v (MkMap []) = MkMap [(new_k, new_v)]
  mapInsertWith f new_k new_v (MkMap ((old_k,old_v):old_kvs)) =
    if old_k == new_k
       then MkMap ((new_k,f new_v old_v):old_kvs)
       else case mapInsertWith f new_k new_v (MkMap old_kvs) of
              MkMap kvs -> MkMap ((old_k,old_v):kvs)

  mapUnion :: Eq k => Map k v -> Map k v -> Map k v
  mapUnion = mapUnionWith const

  mapUnionWith :: Eq k => (v -> v -> v) -> Map k v -> Map k v -> Map k v
  -- mapUnionWith f (MkMap m1) m2 = foldr (\(k,v) -> mapInsertWith f k v) m2 m1
  mapUnionWith _ (MkMap [])           m2 = m2
  mapUnionWith f (MkMap ((mk,mv):m1)) m2 = mapInsertWith f mk mv (mapUnionWith f (MkMap m1) m2)

  instance (Eq k, JoinSemiLattice v) => JoinSemiLattice (Map k v) where
    (\/) = mapUnionWith (\/)

  instance (Eq k, JoinSemiLattice v) => BoundedJoinSemiLattice (Map k v) where
    bottom = mapEmpty
  |])

mapInsertWithNonEmpty :: forall k v (f :: v ~> v ~> v) (old_k :: k) (old_v :: v) (old_kvs :: [(k,v)])
                                    (new_k :: k) (new_v :: v) (m :: Map k v).
                         SEq k
                      => Sing f -> Sing new_k -> Sing new_v -> Sing m
                      -> m :~: MkMap ('(old_k,old_v) : old_kvs)
                      -> Refuted (MapInsertWith f new_k new_v m :~: MapEmpty)
mapInsertWithNonEmpty sf snew_k snew_v (SMkMap sm) Refl Refl
  | STuple2 sold_k _ `SCons` sold_kvs <- sm
  {-
  , SFalse <- sold_k %== snew_k
  = case sMapInsertWith sf snew_k snew_v (SMkMap sold_kvs) of {}
  -}
  = case sold_k %== snew_k of
      SFalse ->
        case sMapInsertWith sf snew_k snew_v (SMkMap sold_kvs) of {}

{-
mapUnionWithNonEmpty :: forall k v (f :: v ~> v ~> v) (kk :: k) (vv :: v) (kkvvs :: [(k,v)])
                                   (m1 :: Map k v) (m2 :: Map k v).
                        Sing f -> Sing m1 -> Sing m2
                     -> m2 :~: MkMap ('(kk,vv) : kkvvs)
                     -> Refuted (MapUnionWith f m1 m2 :~: MapEmpty)
mapUnionWithNonEmpty sf (SMkMap m1) (SMkMap m2) Refl Refl =
  case (m1, m2) of
    (SCons
-}

{-
mapUnionNonEmpty _ (SMkMap SNil)    (SMkMap _) r = case r of {}
mapUnionNonEmpty _ (SMkMap SCons{}) (SMkMap m2) Refl =
  case m2 of
    SCons{} -> undefined
-}

{-
instance (VEq k, VJoinSemiLattice v) => VJoinSemiLattice (Map k v) where
  jslIdempotency m@(SMkMap sm) =
    case sm of
      SNil -> Refl
      STuple2 sk sv `SCons` skvs ->
        case sMapUnionWith (singFun2 @(\/@#@$) (%\/)) (SMkMap skvs) m of
          SMkMap smr ->
            case smr of
              SCons{} -> undefined
-}
