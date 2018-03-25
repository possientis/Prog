import Data.List (isPrefixOf)
import System.Process (callCommand)
import Control.Monad.Trans
import System.Console.Repline


type Repl a = HaskelineT IO a

-- Evaluation : handle each line user inputs
cmd :: String -> Repl ()
cmd input = liftIO $ print input


-- Tab completion : return a completion for parial words entered
completer :: Monad m => WordCompleter m
completer n = do
    let names = ["kirk","spock","mccoy"]
    return $ filter (isPrefixOf n) names

-- Commands
help :: [String] -> Repl ()
help args = liftIO $ print $ "Help: " ++ show args


say :: [String] -> Repl ()
say args = do
    _ <- liftIO $ callCommand $ "cowsay" ++ " " ++ (unwords args)
    return ()

options :: [(String,[String] -> Repl ())]
options = [ ("help",help) , ("say", say) ]


ini :: Repl ()
ini = liftIO $ putStrLn "Welcome!"

repl :: IO ()
repl = evalRepl ">>> " cmd options (Word0 completer) ini

main :: IO ()
main = repl


