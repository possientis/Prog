module BloomFilter.Mutable
  (
    MutBloom
  , elem
  , notElem
  , insert
  , length
  , new
  ) where

import BloomFilter.Internal (MutBloom(..))
import Control.Monad (liftM)
import Control.Monad.ST (ST)
import Data.Array.MArray (getBounds, newArray, readArray, writeArray)
import Data.Word (Word32)
import Prelude hiding (elem, length, notElem)

new :: (a -> [Word32]) -> Word32 -> ST s (MutBloom s a)
new hash numBits = MB hash `liftM` newArray (0, numBits-1) False

length :: MutBloom s a -> ST s Word32
length filt = (succ . snd) `liftM` getBounds (mutArray filt)

insert :: MutBloom s a -> a -> ST s ()
insert filt elt = indices filt elt >>= 
                  mapM_ (\bit -> writeArray (mutArray filt) bit True)

indices :: MutBloom s a -> a -> ST s [Word32]
indices filt elt  = do
  modulus <- length filt
  return $ map (`mod` modulus) (mutHash filt elt)

elem, notElem :: a -> MutBloom s a -> ST s Bool

elem elt filt = indices  filt elt >>= 
                allM (readArray (mutArray filt))

notElem elt filt = not `liftM` elem elt filt

allM :: Monad m => (a -> m Bool) -> [a] -> m Bool
allM p (x:xs) = do
  ok <- p x
  if ok
    then allM p xs
    else return False
allM _ [] = return True





  
