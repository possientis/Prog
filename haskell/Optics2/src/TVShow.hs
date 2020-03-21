{-# LANGUAGE RankNTypes         #-}
{-# LANGUAGE TemplateHaskell    #-}

module  TVShow
    (   name
    ,   birthYear
    ,   title
    ,   numEpisodes
    ,   numSeasons
    ,   criticScore
    ,   actors
    ,   Actor
    ,   TVShow
    ,   howIMetYourMother
    ,   buffy
    ,   tvShows
    ,   ex1, ex2, ex3, ex4, ex5, ex6, ex7, ex8, ex9, ex10
    ,   comparingOf
    ,   ageSummary
    ,   ex11, ex12, ex13, ex14, ex15, ex16, ex17, ex18, ex19
    )   where


import Data.Map         as M
import Data.Ord         (comparing)
import Data.Monoid
import Control.Lens

data Actor = Actor
    { _name      :: String
    , _birthYear :: Int
    } deriving (Show, Eq)

makeLenses ''Actor


data TVShow = TVShow
    { _title        :: String
    , _numEpisodes  :: Int
    , _numSeasons   :: Int
    , _criticScore  :: Double
    , _actors       :: [Actor]
    } deriving (Show, Eq)

makeLenses ''TVShow

howIMetYourMother :: TVShow
howIMetYourMother  = TVShow
    { _title       = "How I Met Your Mother"
    , _numEpisodes = 208
    , _numSeasons  = 9
    , _criticScore = 83
    , _actors      = 
        [ Actor "Josh Radnor" 1974
        , Actor "Cobie Smulders" 1982
        , Actor "Neil Patrick Harris" 1973
        , Actor "Alyson Hannigan" 1974
        , Actor "Jason Segel" 1980
        ]
    }

buffy :: TVShow
buffy  = TVShow
    { _title = "Buffy the Vampire Slayer"
    , _numEpisodes = 144
    , _numSeasons = 7
    , _criticScore = 81
    , _actors =
        [ Actor "Sarah Michelle Gellar" 1977
        , Actor "Alyson Hannigan" 1974
        , Actor "Nicholas Brendon" 1971
        , Actor "David Boreanaz" 1969
        , Actor "Antony Head" 1954
        ]
    }


tvShows :: [TVShow]
tvShows  = [howIMetYourMother, buffy]

-- total number of episodes
ex1 :: Int
ex1 = sumOf (folded . numEpisodes) tvShows

-- best critic score
ex2 :: Maybe Double
ex2 = maximumOf (folded . criticScore) tvShows

-- maximumBy :: Foldable t => (a -> a -> Ordering) -> t a -> a 
-- maximumByOf :: Fold s a -> (a -> a -> Ordering) -> s -> Maybe a
-- comparing :: Ord a => (b -> a) -> b -> b -> Ordering

-- title of the show with the highest critic score
ex3 :: Maybe String
ex3 = _title <$> maximumByOf folded (comparing _criticScore) tvShows

-- oldest actor
ex4 :: Maybe Actor
ex4 = minimumByOf (folded . actors . folded) (comparing _birthYear) tvShows

comparingOf :: Ord a => Lens' s a -> s -> s -> Ordering
comparingOf l = comparing (view l)

-- oldest actor
ex5 :: Maybe Actor
ex5 = minimumByOf (folded . actors . folded) (comparingOf birthYear) tvShows


-- traverse_ :: (Foldable t, Applicative f) => (a -> f b) -> t a -> f ()
-- for_      :: (Foldable t, Applicative f) => t a -> (a -> f b) -> f ()
--
-- traverseOf_ :: Functor f => Fold s a -> (a -> f r) -> s -> f ()
-- forOf_      :: Functor f => Fold s a -> s -> (a -> f r) -> f ()
--

calcAge :: Actor -> Int
calcAge actor = 2030 - _birthYear actor

showActor :: Actor -> String
showActor actor = _name actor <> ": " <> show (calcAge actor)

ex6 :: IO ()
ex6 = traverseOf_ (folded . actors . folded . to showActor) putStrLn tvShows


-- foldOf    :: Monoid a => Fold s a -> s -> a
-- foldMapOf :: Monoid m => Fold s a -> (a -> m) -> s -> m
--
-- Real signatures:
-- foldOf    :: Getting a s a -> s -> a
-- foldMapOf :: Getting m s a -> (a -> m) -> s -> m

ageSummary :: Actor -> (Sum Int, Sum Int)
ageSummary actor = (Sum 1 , Sum (calcAge actor))


ex7 :: (Sum Int, Sum Int)
ex7 = foldOf (folded . actors . folded . to ageSummary) tvShows

computeAverage :: (Sum Int, Sum Int) -> Double
computeAverage (Sum count, Sum total) = fromIntegral total / fromIntegral count


ex8 :: Double
ex8 = computeAverage $ foldOf (folded . actors . folded . to ageSummary) tvShows

ex9 :: Double
ex9 = computeAverage $ foldMapOf (folded . actors . folded) ageSummary tvShows


ex10 :: Map String Int
ex10 = foldMapOf (folded . actors . folded . name) (\n -> M.singleton n 1) tvShows

-- M.unionWith :: Ord k => (a -> a -> a) -> Map k a -> Map k a -> Map k a

ex11 :: Map String Int
ex11 = unionWith (+) (M.singleton "an actor" 1) (M.singleton "an actor" 1)

-- foldByOf    :: Fold s a -> (a -> a -> a) -> a -> s -> a
-- foldMapByOf :: Fold s a -> (r -> r -> r) -> r -> (a -> r) -> s -> r
-- foldrOf     :: Fold s a -> (a -> r -> r) -> r -> s -> r
-- foldlOf     :: Fold s a -> (r -> a -> r) -> r -> s -> r

ex12 :: Map String Int
ex12 = foldMapByOf 
    (folded . actors . folded . name)   -- focus each actor's name
    (unionWith (+))                     -- combine duplicate keys with addition
    mempty                              -- start with the empty map
    (flip M.singleton 1)                -- inject names into maps with count of 1
    tvShows 

ex13 :: Bool
ex13 = has folded [] 

ex14 :: String
ex14 = foldOf both ("Yo", "Adrian!")

ex15 :: Bool
ex15 = elemOf each "phone" ("E.T.", "phone", "home")

ex16 :: Maybe Int 
ex16 = minimumOf folded [5,7,2,3,13,17,11]

ex17 :: Maybe Int 
ex17 = lastOf folded [5,7,2,3,13,17,11]

ex18 :: Bool
ex18 = anyOf folded ((> 9) . length) ["Bulbasaur", "Charmander", "Squirtle"]

ex19 :: Maybe Int
ex19 = findOf folded even [11,22,3,5,6]

