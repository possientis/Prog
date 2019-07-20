module TicTacToe
    (   main
    ,   TicTacToe  (..)
    ,   TicTacToe2 (..)
    ,   emptyBoard
    ,   emptyBoard2
    )   where

main :: IO ()
main = return ()


data TicTacToe a = TicTacToe
    { topLeft   :: a
    , topCenter :: a
    , topRight  :: a
    , midLeft   :: a
    , midCenter :: a
    , midRight  :: a
    , botLeft   :: a
    , botCenter :: a
    , botRight  :: a
    }


emptyBoard :: TicTacToe (Maybe Bool)
emptyBoard = TicTacToe
    Nothing Nothing Nothing
    Nothing Nothing Nothing
    Nothing Nothing Nothing

data Three = One | Two | Three
    deriving (Eq, Ord, Enum, Bounded)


data TicTacToe2 a = TicTacToe2 { board :: Three -> Three -> a }

emptyBoard2 :: TicTacToe2 (Maybe Bool)
emptyBoard2  = TicTacToe2 $ const $ const Nothing
