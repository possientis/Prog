import Control.Concurrent
import Control.Exception (Exception, try)
import qualified Data.Map as M

data ThreadStatus = Running
                  | Finished        -- terminated normally
                  | Threw Exception -- killed by uncaught exception
                    deriving (Eq, Show)
