{-# LANGUAGE TypeFamilies #-}

class IsList l where
    type Item l
    fromList :: [Item l] -> l
    toList   :: l -> [Item l]


instance IsList [a] where
    type Item [a] = a
    fromList = id
    toList   = id



