import Control.DeepSeq

{-
deepseq :: NFData a => a -> b -> b
force   :: NFData a => a -> a
-}

--evaluation yields ()
test1 = [1,undefined] `seq` () 

-- evaluation will fail
test2 = [1::Int,undefined] `deepseq` ()
