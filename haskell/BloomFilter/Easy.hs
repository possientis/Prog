easyList  :: (Hashable a) 
          => Double       -- false positive rate (between 0 and 1)
          -> [a]          -- values to populate the filter with
          -> Either String (B.Bloom a) 
