import Test.Tasty
import Test.Tasty.HUnit
import System.IO.Silently


test :: Int -> IO ()
test n = print (n * n)

-- capture :: IO a -> IO (String, a)

testCapture :: Int -> IO ()
testCapture n = do
    (stdout, result) <- capture (test n)
    assert $ result == ()
    assert $ stdout == (show (n * n) ++ "\n")


suite :: TestTree
suite = testGroup "TestSuite" 
    [ testGroup "Units" 
        [ testCase "Equality" $ testCapture 10
        ]
    ]
    

main :: IO ()
main = defaultMain suite
