import Data.Tree
import Data.Graph


data Grph node key = Grph
    { _graph    :: Graph
    , _vertices :: Vertex -> (node, key, [key])
    }

fromList :: Ord key => [(node,key,[key])] -> Grph node key
fromList = uncurry Grph . graphFromEdges'

-- TODO
