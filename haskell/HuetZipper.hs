type Item = String

data Tree = Item Item | Section [Tree]

data Path = Top | Node [Tree] Path [Tree]


data Location = Loc Tree Path

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
 



   
