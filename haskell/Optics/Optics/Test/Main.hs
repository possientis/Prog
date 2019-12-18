module  Optics.Test.Main
    (   specMain
    )   where


import Test.Hspec

import Optics.Test.Fin
import Optics.Test.Bool
import Optics.Test.FinVec
import Optics.Test.Adapter

specMain :: Spec
specMain = do
    specFin
    specBool
    specFinVec
    specAdapter
