module Eval.App
  ( runApp
  ) where

import Core.Free
import Eval.Logger
import Lang.App

evalAppF :: AppF a -> IO a
evalAppF (EvalLogger logAct next) = do
  runLogger logAct 
  pure $ next ()

runApp :: App a -> IO a
runApp = foldFree evalAppF 
