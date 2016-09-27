module BloomFilter.Easy
  (
    suggestSizing
  , sizings
  , easyList
  -- re-export useful names from BloomFilter
  , B.Bloom
  , B.length
  , B.elem
  , B.notElem
  ) where

import BloomFilter.Hash (Hashable, doubleHash)
import qualified BloomFilter as B

easyList  :: (Hashable a) 
          => Double       -- false positive rate (between 0 and 1)
          -> [a]          -- values to populate the filter with
          -> Either String (B.Bloom a) 
easyList = undefined

