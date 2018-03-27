{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

import Language.Haskell.TH

-- Expression 
ex1 :: IO Exp   
ex1 = runQ [e| \x -> x |]
-- LamE [VarP x_0] (VarE x_0)

ex1' :: IO Exp
ex1' = runQ [| \x -> x |]       -- 'e' optional
-- LamE [VarP x_0] (VarE x_0)

-- Declaration
ex2 :: IO [Dec] 
ex2 = runQ [d| data Nat = Z | S Nat |]
-- [DataD [] Nat_0 [] Nothing [NormalC Z_1 [],NormalC S_2 [(Bang NoSourceUnpackedness NoSourceStrictness,ConT Nat_0)]] []]

data Nat' = Z' | S' Nat'

-- Pattern
ex3 :: IO Pat
ex3 = runQ [p| S' (S' Z') |]
-- ConP Main.S' [ConP Main.S' [ConP Main.Z' []]]

-- Type
ex4 :: IO Type
ex4 = runQ [t| Int -> [Int] |]
-- AppT (AppT ArrowT (ConT GHC.Types.Int)) (AppT ListT (ConT GHC.Types.Int))

ex5 = $(runQ [| \x -> x |]) 3
-- 3

-- builds the function (f = \(a,b) -> a)
f :: Q [Dec]
f = do
    let f = mkName "f"
    a <- newName "a"
    b <- newName "b"
    return [ FunD f [ Clause [ TupP [VarP a, VarP b]] (NormalB (VarE a)) [] ] ]

ex6 :: IO [Dec]
ex6 = runQ f
-- [FunD f [Clause [TupP [VarP a_0,VarP b_1]] (NormalB (VarE a_0)) []]]




