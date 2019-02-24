module  Tag
    (   Tag (..) 
    )   where

import Name

data TagType = C | F | P Int
    deriving (Eq, Ord, Show)
 
data Tag = Tag
    { tagType :: TagType
    , tagName :: Name
    }
    deriving (Eq, Ord, Show)




    
