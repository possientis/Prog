-- rnf unknown
module LineChunks
(
chunkedReadWith
) where


import Control.Exception (bracket, finally)
import Control.Monad (forM, liftM)
import Control.Parallel.Strategies (NFData, rnf)
import Data.Int (Int64)
import qualified Data.ByteString.Lazy.Char8 as LB
import GHC.Conc (numCapabilities)
import System.IO







