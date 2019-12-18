module  Optics.Test.Main
    (   specMain
    )   where


import Test.Hspec

import Optics.Test.If
import Optics.Test.Nat
import Optics.Test.Fin
import Optics.Test.Vec
import Optics.Test.Leq
import Optics.Test.Bool
import Optics.Test.Lens
import Optics.Test.Plus
import Optics.Test.Prism
import Optics.Test.IsEven
import Optics.Test.FinVec
import Optics.Test.FunList
import Optics.Test.Adapter

specMain :: Spec
specMain = do
    specIf
    specNat
    specFin
    specVec
    specLeq
    specBool
    specLens
    specPlus
    specPrism
    specIsEven
    specFinVec
    specAdapter
    specFunList
