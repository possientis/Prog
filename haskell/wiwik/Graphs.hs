import Data.Tree
import Data.Graph


data Grph node key = Grph
    { _graph    :: Graph
    , _vertices :: Vertex -> (node, key, [key])
    }

fromList :: Ord key => [(node,key,[key])] -> Grph node key
fromList = uncurry Grph . graphFromEdges'

vertexLabel :: Grph b t -> Vertex -> b
vertexLabel g = (\(vi, _, _) -> vi) . (_vertices g)

vertexLabels :: Functor f => Grph b t -> (f Vertex) -> f b
vertexLabels g = fmap (vertexLabel g)


-- topologically sort graph
topo' :: Grph node key -> [node]
topo' g = vertexLabels g $ topSort (_graph g)


-- strongly connected components of graph
scc' :: Grph node key -> [[node]]
scc' g = fmap (vertexLabels g . flatten) $ scc (_graph g)

ex1 :: [(String, String, [String])]
ex1 =   [   ("a","a",["b"])
        ,   ("b","b",["c"])
        ,   ("c","c",["a"])
        ]

ts1 :: [String]
ts1 = topo' $ fromList ex1
-- ["a","b","c"]

sc1 :: [[String]]
sc1 = scc' $ fromList ex1
-- [["a","b","c"]]

ex2 :: [(String,String,[String])]
ex2 = ex1   ++  [   ("d","d",["e"])
                ,   ("e","e",["f","e"])
                ,   ("f","f",["d","e"])
                ]

ts2 :: [String]
ts2 = topo' $ fromList ex2
-- ["d","e","f","a","b","c"]

sc2 :: [[String]]
sc2 = scc' $ fromList ex2
--[["d","e","f"],["a","b","c"]]



