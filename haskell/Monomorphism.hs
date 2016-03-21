--{-# NoMonomorphismRestriction #-} -- unrecognized ??

--myShow = show -- won't compile for some reason
myShow2 value = show value  -- this is fine for some reason

myShow3 :: (Show a) => a -> String
myShow3 = show              -- this is fine also
