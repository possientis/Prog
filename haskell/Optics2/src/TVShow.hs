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
    ,   ex1, ex2, ex3, ex4, ex5, ex6
    ,   comparingOf
    )   where

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

