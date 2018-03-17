{-# LANGUAGE ExplicitForAll #-}

module Compose (compose) where

compose :: forall a b c. (b -> c) -> (a -> b) -> a -> c
compose g f = \x -> g (f x)

{- core: ghc -c  -ddump-simpl
compose :: forall a b c. (b -> c) -> (a -> b) -> a -> c
compose = \ (@ a) (@ b) (@ c) (g :: b -> c) (f :: a -> b) (x :: a) -> g (f x)
-}

{- stg: ghc -c -ddump-stg
Compose.compose :: forall a b c. (b -> c) -> (a -> b) -> a -> c =
    \r [g f x] let { y :: b = \u [] f x; } in  g y;
-}
