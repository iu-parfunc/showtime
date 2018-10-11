{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
module Showtime.Verified.Lattice where

import Algebra.Lattice
import Data.Singletons.TH

$(singletonsOnly [d|

  -- -| A algebraic structure with element joins: <http://en.wikipedia.org/wiki/Semilattice>
  --
  -- > Associativity: x \/ (y \/ z) == (x \/ y) \/ z
  -- > Commutativity: x \/ y == y \/ x
  -- > Idempotency:   x \/ x == x
  class JoinSemiLattice a where
      infixr 5 \/
      (\/) :: a -> a -> a

  -- -| A join-semilattice with an identity element 'bottom' for '\/'.
  --
  -- > Identity: x \/ bottom == x
  class JoinSemiLattice a => BoundedJoinSemiLattice a where
      bottom :: a
  |])

$(singletonsOnly [d|
  instance JoinSemiLattice () where
    _ \/ _ = ()

  instance BoundedJoinSemiLattice () where
    bottom = ()
  |])

class (JoinSemiLattice a, PJoinSemiLattice a, SJoinSemiLattice a)
    => VJoinSemiLattice a where
  jslAssociativity :: forall (x :: a) (y :: a) (z :: a).
                      Sing x -> Sing y -> Sing z
                   -> (x \/ (y \/ z)) :~: ((x \/ y) \/ z)

  jslCommutativity :: forall (x :: a) (y :: a).
                      Sing x -> Sing y
                   -> (x \/ y) :~: (y \/ x)

  jslIdempotency :: forall (x :: a). Sing x
                 -> (x \/ x) :~: x

class ( BoundedJoinSemiLattice a, PBoundedJoinSemiLattice a
      , SBoundedJoinSemiLattice a, VJoinSemiLattice a )
    => VBoundedJoinSemiLattice a where
  bjslIdentity :: forall (x :: a). Sing x
               -> (x \/ Bottom) :~: x

instance VJoinSemiLattice () where
  jslAssociativity _ _ _ = Refl
  jslCommutativity _ _ = Refl
  jslIdempotency STuple0 = Refl

instance VBoundedJoinSemiLattice () where
  bjslIdentity STuple0 = Refl
