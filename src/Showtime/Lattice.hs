{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
module Showtime.Lattice where

import Data.Singletons.TH

$(singletons [d|

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
