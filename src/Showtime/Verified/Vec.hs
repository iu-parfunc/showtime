{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
module Showtime.Verified.Vec where

import Algebra.Lattice
import Data.Kind
import Data.Nat
import Data.Singletons.TH
import Showtime.Verified.Lattice

data Vec :: Nat -> Type -> Type where
  VNil :: Vec Z a
  (:>) :: a -> Vec n a -> Vec (S n) a
infixr 5 :>

data instance Sing :: forall n a. Vec n a -> Type where
  SVNil :: Sing VNil
  (:%>) :: Sing x -> Sing xs -> Sing (x :> xs)
infixr 5 :%>
$(genDefunSymbols [''Vec])

deriving instance Eq a => Eq (Vec n a)
deriving instance Ord a => Ord (Vec n a)
deriving instance Show a => Show (Vec n a)
deriving instance Foldable (Vec n)
deriving instance Functor (Vec n)
deriving instance Traversable (Vec n)

$(singletons [d|
  instance JoinSemiLattice a => JoinSemiLattice (Vec n a) where
    VNil \/ VNil = VNil
    (x :> xs) \/ (y :> ys) = (x \/ y) :> (xs \/ ys)
  |])

instance VJoinSemiLattice a => VJoinSemiLattice (Vec n a) where
  jslAssociativity SVNil SVNil SVNil = Refl
  jslAssociativity (x :%> xs) (y :%> ys) (z :%> zs)
    | Refl <- jslAssociativity x y z
    , Refl <- jslAssociativity xs ys zs
    = Refl

  jslCommutativity SVNil SVNil = Refl
  jslCommutativity (x :%> xs) (y :%> ys)
    | Refl <- jslCommutativity x y
    , Refl <- jslCommutativity xs ys
    = Refl

  jslIdempotency SVNil = Refl
  jslIdempotency (x :%> xs)
    | Refl <- jslIdempotency x
    , Refl <- jslIdempotency xs
    = Refl

replicateV :: Sing (n :: Nat) -> a -> Vec n a
replicateV SZ      _ = VNil
replicateV (SS sn) x = x :> replicateV sn x

type family ReplicateV (n :: Nat) (x :: a) :: Vec n a where
  ReplicateV Z     _ = VNil
  ReplicateV (S n) x = x :> ReplicateV n x

sReplicateV :: Sing (n :: Nat) -> Sing (x :: a) -> Sing (ReplicateV n x)
sReplicateV SZ      _  = SVNil
sReplicateV (SS sn) sx = sx :%> sReplicateV sn sx

instance (SingI n, BoundedJoinSemiLattice a) => BoundedJoinSemiLattice (Vec n a) where
  bottom = replicateV (sing :: Sing n) bottom

instance PBoundedJoinSemiLattice a => PBoundedJoinSemiLattice (Vec n a) where
  type Bottom = (ReplicateV n Bottom :: Vec n a)

instance (SingI n, SBoundedJoinSemiLattice a) => SBoundedJoinSemiLattice (Vec n a) where
  sBottom = sReplicateV (sing :: Sing n) sBottom

instance (SingI n, VBoundedJoinSemiLattice a) => VBoundedJoinSemiLattice (Vec n a) where
  bjslIdentity SVNil = Refl
  bjslIdentity (x :%> xs)
    | Refl  <- bjslIdentity x
    , SS sn <- sing :: Sing n
    , Refl  <- withSingI sn $ bjslIdentity xs
    = Refl
