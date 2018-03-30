{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}

import Language.Haskell.TH
import Text.Show.Pretty (ppShow)

introspect :: Name -> Q Exp
introspect n = do
    t <- reify n
    runIO $ putStrLn $ ppShow t
    [| return () |]

-- ghci -XTemplateHaskell %
--
-- *Main> $(instrospect 'id)
{-
VarI
  GHC.Base.id
  (ForallT
     [ KindedTV a_1627410282 StarT ]
     []
     (AppT (AppT ArrowT (VarT a_1627410282)) (VarT a_1627410282)))
  Nothing
-}

-- *Main> $(introspect ''Maybe)

{-
TyConI
  (DataD
     []
     GHC.Base.Maybe
     [ KindedTV a_822083586 StarT ]
     Nothing
     [ NormalC GHC.Base.Nothing  []
     , NormalC
         GHC.Base.Just
         [ ( Bang NoSourceUnpackedness NoSourceStrictness
           , VarT a_822083586
           )
         ]
     ]
      
     [])
-}
