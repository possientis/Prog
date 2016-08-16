module PodTypes where

data Podcast = Podcast { 
  castId :: Integer,      -- ^ Numeric ID for this podcast
  castURL :: String       -- ^ Its feed URL
} deriving (Eq, Show, Read)

data Episode = Episode {
  epId :: Integer,        -- ^ Numeric ID for this episode
  epCast :: Podcast,      -- ^ The podcast it came from
  epURL :: String,        -- ^ the download URL fir this episode
  epDone :: Bool          -- ^ whether or not we are done with it
} deriving (Eq, Show, Read)



