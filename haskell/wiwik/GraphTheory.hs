import Data.Graph.Inductive     -- libghc-fgl-dev


cyg3 :: Gr Char String
cyg3    = buildGr
        [ ([("ca",3)],1,'a',[("ab",2)])
        , ([],2,'b',[("bc",3)])
        , ([],3,'c',[])
        ]

-- loop query
ex1 :: Bool
ex1 = hasLoop x


x :: Gr Int ()
x = insEdges edges gr where
    gr = insNodes nodes empty
    edges = [(0,1,()), (0,2,()), (2,1,()), (2,3,())]
    nodes = zip [0,1 ..] [2,3,4,1]

-- Dominators
ex2 :: [(Node,[Node])]
ex2 = dom x 0
-- [(0,[0]),(1,[1,0]),(2,[2,0]),(3,[3,2,0])]
 
