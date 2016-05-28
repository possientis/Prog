module PNM(Greymap(..)) where 

import qualified Data.ByteString.Lazy.Char8 as L8
import qualified Data.ByteString.Lazy as L
import Data.Char (isSpace)


data Greymap = Greymap {
  greyWidth   :: Int,
  greyHeight  :: Int,
  greyMax     :: Int, -- should be Word8
  greyData    :: L.ByteString
} deriving Eq


instance Show Greymap where
  show (Greymap w h m _) =  "Greymap " ++ show w ++ "x" ++ show h ++ 
                            " " ++ show m
matchHeader :: L.ByteString -> L.ByteString -> Maybe L.ByteString
matchHeader prefix str
  | prefix `L8.isPrefixOf` str
    = Just (L8.dropWhile isSpace (L.drop (L.length prefix) str))
  | otherwise
    = Nothing

getNat :: L.ByteString -> Maybe (Int, L.ByteString)
getNat s = case L8.readInt s of
              Nothing         -> Nothing
              Just (num,rest)
                | num <= 0    -> Nothing
                | otherwise   -> Just (fromIntegral num, rest)  -- why fromIntegral?
  

getBytes :: Int -> L.ByteString -> Maybe (L.ByteString, L.ByteString)
getBytes n str  = let count             = fromIntegral n
                      both@(prefix, _)  = L.splitAt count str
                  in if L.length prefix < count
                        then Nothing
                        else Just both



-- 'This function is begging for some abstraction and refactoring'
parseP5 :: L.ByteString -> Maybe (Greymap, L.ByteString)
parseP5 s =
  case matchHeader (L8.pack "P5") s of
    Nothing -> Nothing
    Just s1 ->
      case getNat s1 of
        Nothing           -> Nothing
        Just (width, s2)  ->
          case getNat (L8.dropWhile isSpace s2) of
            Nothing           -> Nothing
            Just (height, s3) ->
              case getNat (L8.dropWhile isSpace s3) of
                Nothing           -> Nothing
                Just (maxGrey, s4)
                  | maxGrey > 255 -> Nothing
                  | otherwise     -> 
                  case getBytes 1 s4 of
                    Nothing       -> Nothing
                    Just (_,s5)   -> 
                      case getBytes (width*height) s5 of
                        Nothing           -> Nothing
                        Just (bitmap, s6) ->    
                          Just (Greymap width height maxGrey bitmap, s6)


-- no 'fixity' declared , so defaults to infixl 9 
-- (i.e. left-associative, strongest operator precedence )
(>>?) :: Maybe a -> (a -> Maybe b) -> Maybe b
Nothing >>? _ = Nothing
Just v >>? f  = f v

parse5_take2 :: L.ByteString -> Maybe (Greymap, L.ByteString)
parse5_take2 s = 
  matchHeader (L8.pack "P5") s  >>?
  \s  -> skipSpace ((), s)      >>?
  (getNat.snd)                  >>?
  skipSpace                     >>?
  \(width, s) -> getNat s       >>?
  skipSpace                     >>?
  \(height, s) -> getNat s      >>?
  \(maxGrey,s) -> getBytes 1 s  >>?
  (getBytes (width*height).snd) >>?
  \(bitmap, s) -> Just (Greymap width height maxGrey bitmap, s)


skipSpace :: (a, L.ByteString) -> Maybe (a, L.ByteString)
skipSpace (a,s) = Just (a, L8.dropWhile isSpace s)








