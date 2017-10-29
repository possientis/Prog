{-# LANGUAGE GeneralizedNewtypeDeriving #-}

import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.State

type Stack      = [Int]
type Output     = [Int]
type Program    = [Instr] 

type VM a = ReaderT Program (WriterT Output (State Stack)) a


newtype Comp a = Comp { unComp :: VM a }
    deriving    (   Functor 
                ,   Applicative  
                ,   Monad
                ,   MonadReader Program
                ,   MonadWriter Output
                ,   MonadState Stack
                )

data Instr = Push Int | Pop | Puts | Add

-- modify :: MonadState s m => (s -> s) -> m ()
-- gets   :: MonadState s m => (s -> a) -> m a
-- tell   :: MonadWriter w m => w -> m ()

evalInstr :: Instr -> Comp ()
evalInstr instr = case instr of
    Pop     ->  modify tail
    Push n  ->  modify (n:)
    Puts    ->  do
        tos <- gets head
        tell [tos]
    Add     -> do
        x   <- gets (head . tail)
        y   <- gets head
        modify (x+y:) 

-- ask      :: MonadReader r m => m r
-- local    :: MonadReader r m => (r -> r) -> m a -> m a

eval :: Comp ()
eval = do
    instr <- ask
    case instr of
        []      -> return ()
        (i:is)  -> evalInstr i >> local (const is) eval

-- runReaderT  :: (Monad m) => ReaderT r m a -> r -> m a
-- execWriterT :: (Monad m) => WriterT w m a -> m w 
-- evalState   :: State s a -> s -> a
execVM :: Program -> Output
execVM = flip evalState [] . execWriterT . runReaderT (unComp eval)


program :: Program
program =   [   Push 42
            ,   Push 27
            ,   Add
            ,   Puts 
            ,   Pop
            ,   Puts
            ,   Pop
            ,   Puts
            ,   Pop
            ]

main :: IO ()
main = mapM_ print $ execVM program


