import qualified Data.ByteString.Lazy as L

-- a byte sequence which identifies a file's type is often called 'magic number'
-- Word8 is the Haskell data type for representing bytes

-- this does not perform IO
hasElfMagic :: L.ByteString -> Bool
hasElfMagic content = L.take 4 content == elfMagic
  where elfMagic = L.pack [0x7f, 0x45, 0x4c, 0x46] 


-- pack :: [Word8] -> ByteString
-- unpack:: ByteString -> [Word8]


isElfFile :: FilePath -> IO Bool
isElfFile path = do
  content <- L.readFile path
  return (hasElfMagic content)

