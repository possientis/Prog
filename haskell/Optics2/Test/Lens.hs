module Test.Lens
  ( main
  , spec
  ) where

import Test.Hspec

import Lens
import Optic

main :: IO ()
main = hspec spec

spec :: Spec
spec = describe "Testing Lens" $ do
  spec_1

spec_1 :: Spec
spec_1 = describe "_1" $ do
  it "getL _1 (\"a\",\"aa\") is \"a\"" $ do
    getL _1 ("a","aa") `shouldBe` "a" 
  it "setL _1 \"b\" (\"a\",\"aa\") is (\"b\",\"aa\")" $ do
    setL _1 "b" ("a","aa") `shouldBe` ("b","aa")
  it "overL _1 (++\"b\") (\"a\",\"aa\") is (\"ab\",\"aa\")" $ do
    overL _1 (++"b") ("a","aa") `shouldBe` ("ab","aa")
  it "over _1 (++\"b\") (\"a\",\"aa\") is (\"ab\",\"aa\")" $ do
    over _1 (++"b") ("a","aa") `shouldBe` ("ab","aa")

