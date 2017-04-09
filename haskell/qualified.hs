import qualified Module1        -- one possible way of resolving name conflicts
import qualified Module2  as M2 -- using 'as' keyword for shorter prefix
import Module1 (bar)            -- 'bar' can now be accessed with 'Module1' prefix


main = do
  Module1.foo
  M2.foo                        -- 'as' keyword useful to minimize typing 
  bar
