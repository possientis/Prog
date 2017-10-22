-- import Control.Monad.Writer
import Control.Monad.Writer.Strict
-- import MonadWriter

type MyWriter = Writer [Int] String

example :: MyWriter
example = do
    tell [1..5]
    tell [5..10]
    return "foo"

output :: (String, [Int])
output = runWriter example
