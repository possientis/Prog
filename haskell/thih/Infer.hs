module  Infer
    (   Infer
    )   where


import TI
import TypeClass
import Assumption

type Infer a b = ClassEnv -> [Assump] -> a -> TI ([Pred],b)
