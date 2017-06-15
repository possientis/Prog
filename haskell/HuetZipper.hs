type Item = String

data Tree = Item Item | Section [Tree]  deriving Show
data Path = Top | Node [Tree] Path [Tree] deriving Show
data Location = Loc Tree Path deriving Show

tree1 = Section
  [ Section [ Item "a", Item "*", Item "b" ]
  , Item "+"
  , Section [ Item "c", Item "*", Item "d" ]
  ]

loc1 = Loc 
  (Item "*") 
  (Node 
    [Item "c"] 
    (Node
      [Item "+", Section [ Item "a", Item "*", Item "b" ]]
      Top
      [])
    [Item "d"])

goLeft :: Location -> Location
goLeft (Loc t p) = case p of
  Top               -> error "goLeft: cannot go left from top position"
  Node (l:ls) up rs -> Loc l (Node ls up (t:rs))
  Node [] up rs     -> error "goLeft: already on left-most position"

goRight :: Location -> Location
goRight (Loc t p) = case p of
  Top               -> error "goRight: cannot go right from top position"
  Node ls up (r:rs) -> Loc r (Node (t:ls) up rs) 
  Node ls up []     -> error "goRight: already on right-most position"
 
goUp :: Location -> Location
goUp (Loc t p)    = case p of
  Top             -> error "goUp: already on top-most position" 
  Node ls up rs   -> Loc (Section $ (reverse ls) ++ (t:rs)) up 

goDown :: Location -> Location
goDown (Loc t p)  = case t of
  Item _          -> error "goDown: already on bottom-most position"
  Section (t1:ts) -> Loc t1 (Node [] p ts)
  Section []      -> error "goDown: there is nothing to go down to"

nthSon :: Location -> Int -> Location
nthSon loc n = go n where
  go 1 = goDown loc
  go n = if n > 0 
    then goRight (go (n - 1)) 
    else error "nthSon expects positive integer"


change :: Location -> Tree -> Location
change (Loc _ p) t  = Loc t p


insertRight :: Location -> Tree -> Location
insertRight = undefined
   
