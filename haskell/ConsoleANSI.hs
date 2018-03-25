import System.Console.ANSI

-- works but colors are often not what you expect, just like with bash
-- guessing terminal does not comply with standard

main :: IO ()
main = do
--    setSGR [SetColor Foreground Dull Blue]
    setSGR [SetColor Background Dull Red]
    putStrLn "Red-On-Blue"
    setSGR [Reset]
    putStrLn "Default colors"
