import Control.Monad.State.Lazy
import Data.Unique
import Data.Maybe
import Prelude hiding (id)
import GHC.Conc.Sync

type WorldM = StateT World IO


data World = World { objects :: [ WorldObject ] }


data WorldObject = WorldObject { id :: Unique }

addObject :: WorldObject -> WorldM ()
addObject w0  = do
  wst <-  get
  put $ World $ w0 : (objects wst)

getObject :: Unique -> WorldM (Maybe WorldObject)
getObject id1 = do
  wst <- get
  return $ listToMaybe $ filter (\w0 -> id w0 == id1) (objects wst)

data WorldChange 
  = NewObj WorldObject 
  | UpdateObj WorldObject 
  | RemoveObj Unique

type ChangeBucket = TVar [ WorldChange ]


mainLoop :: ChangeBucket -> WorldM ()
mainLoop cB = 
  -- do some stuff
  -- it's probably fun
  -- using your cheeky wee WorldM accessors
  mainLoop cB -- recurse on shared variable
