import Data.Typeable
import Data.Data

data Animal = Cat | Dog deriving Typeable

instance Data Animal where
    gfoldl k z Cat = z Cat
    gfoldl k z Dog = z Dog

    gunfold k z c 
        = case constrIndex c of
            1 -> z Cat
            2 -> z Dog

    toConstr Cat = cCat
    toConstr Dog = cDog

    dataTypeOf _ = tAnimal


tAnimal :: DataType
tAnimal = mkDataType "Main.Animal" [cCat, cDog]

cCat :: Constr
cCat = mkConstr tAnimal "Cat" [] Prefix

cDog :: Constr
cDog = mkConstr tAnimal "Dog" [] Prefix

{- duplicate
instance Data a => Data [a] where
    gfoldl _ z []       = z []
    gfoldl k z (x:xs)   = z (:) `k` x `k` xs

    toConstr []         = nilConstr
    toConstr (_:_)      = consConstr

    gunfold k z c
        = case constrIndex c of 
            1 -> z []
            2 -> k (k (z (:)))

    dataTypeOf _ = listDataType


nilConstr :: Constr
nilConstr = mkConstr listDataType "[]" [] Prefix

consConstr :: Constr
consConstr = mkConstr listDataType "(:)" [] Infix

listDataType :: DataType
listDataType = mkDataType "Prelude.[]" [nilConstr,consConstr]
-}

{- duplicate
instance (Data a, Data b) => Data (a,b) where
    gfoldl k z (a,b) = z (,) `k` a `k` b

    toConstr (_,_) = tuple2Constr

    gunfold k z c 
        = case constrIndex c of 
            1 -> k (k (z (,)))

    dataTypeOf _ = tuple2DataType


tuple2Constr :: Constr
tuple2Constr = mkConstr tuple2DataType "(,)" [] Infix

tuple2DataType :: DataType
tuple2DataType = mkDataType "Prelude.(,)" [tuple2Constr]
-}




