module  Syntax
    (   IExp
    ,   CExp
    ,   Name
    ,   T   
    )   where

data IExp    -- Inferable expression
    = Ann CExp T
    | Bound Int
    | Free Name
    | IExp :@: CExp
    deriving (Eq, Show)

data CExp   -- Checkable expression
    = Inf IExp
    | Lam CExp
    deriving (Eq, Show)

data Name
    = Global String
    | Local Int
    | Quote Int
    deriving (Eq, Show)

data T
    = TFree Name
    | Fun T T
    deriving (Eq, Show)


