{-# OPTIONS_GHC -Wno-orphans #-}
module Showtime.OriginalSpec where

import Data.List as L
import Showtime.Original
import Test.Hspec
import Test.QuickCheck

-- A bit of model checking
--------------------------------------------------------------------------------

-- | Note, we don't generate INTERNAL states like BlockedOpen.
instance Arbitrary Op where
  arbitrary =
    oneof
      [ pure Open
      , (Compute . abs) <$> arbitrary
      ]


-- Tests
--------------------------------------------------------------------------------

t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t10b,t11,t12 :: Prog
t0 = [[Open]]
t1 = [[Open],[Open]]
t2 = [[Compute 10,Open],[Open]]
t3 = [[Compute 10,Open],[Compute 10,Open]]
t4 = [[Compute 10,Open],[Compute 9,Open]]
t5 = [[Open],[Open],[Open]]
t6 = [[Compute 10,Open],[Compute 7,Compute 7,Open],[Open,Compute 100]]
-- TID1 make the start of the second show:
t7 = [[Open],[Compute 8,Open]]
-- TID1 make the start of the third show:
t8 = [[Open],[Compute 11,Open]]

t9  = [[Open,Compute 9,Open],[Compute 13,Open]]
t10 = [[Open,Compute 9,Open],[Compute 8,Open]]

t10b = [[Open,Compute 11,Open],[Compute 7,Open]]

t11 = [[Open,Compute 9,Open],[Compute 8,Open],[Compute 8,Open]]

t12 = [[Open,Open],[Open]]

-- t13 = [[],[],[],[]]

main :: IO ()
main = hspec spec

spec :: Spec
spec = do
  describe "Showtime model checker:" $ do
    it "t0: one thread, just open" $ threadOrder t0 `shouldBe` [0]
    it "t1: two threads open" $ threadOrder t1 `shouldBe` [0,1]
    it "t2: delay first" $ threadOrder t2 `shouldBe` [1,0]
    it "t3: symmetric delay" $ threadOrder t3 `shouldBe` [0,1]
    it "t4: asymmetric delay" $ threadOrder t4 `shouldBe` [1,0]
    it "t5: triple open" $ threadOrder t5 `shouldBe` [0,1,2]
    it "t6: more complicated" $ threadOrder t6 `shouldBe` [2,0,1]
    it "t7: delay before expiry" $ threadOrder t7 `shouldBe` [0,1]
    it "t8: delay after expiry" $ threadOrder t8 `shouldBe` [0,1]
    it "t9: double open" $ threadOrder t9 `shouldBe` [0,0,1]
    it "t10: double open, reserved"  $ threadOrder t10  `shouldBe` [0,0,1]
    it "t10b: double open, reserved" $ threadOrder t10b `shouldBe` [0,1,0]
    it "t11: double open, double delay join" $ threadOrder t11 `shouldBe` [0,0,1,2]
    it "t12: double open, no compute" $ threadOrder t12 `shouldBe` [0,0,1]
    it "two empty programs" $ threadOrder [[],[]] `shouldBe` []
    it "three empty programs" $ threadOrder [[],[],[]] `shouldBe` []
--     it "t13: four empty programs" $ threadOrder t13 `shouldBe` []

    it "check an arbitrary program" $
       property $ \p ->
           let p' = L.take numProcs p in -- FIXME: generalize this to more threads!
           case summarize (interp2 (p' :: Prog)) of (_,_) -> True

