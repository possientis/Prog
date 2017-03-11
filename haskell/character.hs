import Data.Char

main :: IO ()
main = do
  putStrLn $ show (map chr [0..255])
  putStrLn $ show (map (ord . chr) [0..255])
