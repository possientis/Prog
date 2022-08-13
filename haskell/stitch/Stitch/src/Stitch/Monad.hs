{-# LANGUAGE FlexibleInstances          #-} -- temp
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE UndecidableInstances       #-} -- temp

module  Stitch.Monad
  ( Stitch 
  , StitchE
  , StitchM (..)
  , eitherToStitchE
  , issueError
  , prompt
  , quit
  , runStitch
  , runStitchE
  ) where

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Trans.Maybe
import System.Console.Haskeline
import System.IO
import Text.PrettyPrint.ANSI.Leijen

import Stitch.Globals
import Stitch.Utils

-- | A monad giving Haskeline-like interaction, access to 'Globals',
-- and the ability to abort with 'mzero'.
newtype Stitch a = Stitch { unStitch :: MaybeT (StateT Globals (InputT IO)) a }
  deriving (Monad, Functor, Applicative, MonadState Globals, MonadIO)

-- | Like the 'Stitch' monad, but also supporting error messages via 'Doc's
newtype StitchE a = StitchE { unStitchE :: ExceptT Doc Stitch a }
  deriving (Monad, Functor, Applicative, MonadState Globals, MonadError Doc)

-- | State monad is also a Reader monad
instance MonadReader Globals StitchE where
  ask = get
  local f run = do
    old <- get            -- current env
    let new = f old       -- modified env
    put new               -- force modifed env
    res <- run            -- run computation in modified env
    put old               -- restore env
    return res            -- return result obtained with modified env

-- | Class for the two stitch monads
class StitchM m where
  -- | Print a 'Doc' without a newline at the end
  printDoc :: Doc -> m ()

  -- | Print a 'Doc' with a newline
  printLine :: Doc -> m ()

instance StitchM Stitch where
  printDoc  = Stitch . liftIO . displayIO stdout . toSimpleDoc
  printLine = Stitch . liftIO . displayIO stdout . toSimpleDoc . (<> hardline)

instance StitchM StitchE where
  printDoc  = StitchE . lift . printDoc
  printLine = StitchE . lift . printLine

-- | Prompt the user for input, returning a string if one is entered.
-- Like 'getInputLine'.
prompt :: String -> Stitch (Maybe String)
prompt  = Stitch . lift . lift . getInputLine

-- | Abort the 'Stitch' monad
quit :: Stitch a
quit = do
  printLine (text "Good-bye.")
  Stitch mzero

-- | Abort the computation with an error
issueError :: Doc -> StitchE a
issueError = StitchE . throwError

-- | Hoist an 'Either' into 'StitchE'
eitherToStitchE :: Either String a -> StitchE a
eitherToStitchE (Left err) = issueError (text err)
eitherToStitchE (Right x)  = return x

-- | Run a 'Stitch' computation
runStitch :: Stitch () -> InputT IO ()
runStitch run
  = void $ flip evalStateT emptyGlobals $ runMaybeT $ unStitch run

-- | Run a 'StitchE' computation
runStitchE :: StitchE a -> Stitch (Either Doc a)
runStitchE run = runExceptT $ unStitchE run
