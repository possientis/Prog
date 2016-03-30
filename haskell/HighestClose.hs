import qualified Data.ByteString.Lazy.Char8 as L

closing = (!!4) . L.split ','
