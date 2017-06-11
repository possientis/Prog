type Item = String

data Tree = Item Item | Section [Tree]

data Path = Top | Node [Tree] Path [Tree]


data Location = Loc Tree Path

tree1 = Section
  [ Section [ Item "a", Item "*", Item "b" ]
  , Item "+"
  , Section [ Item "c", Item "*", Item "d" ]
  ]

   
