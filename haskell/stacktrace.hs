-- ghc -O0 -rtsopts=all -prof -auto-all; ./stacktrace +TRS -xc

import Control.Exception

f x = g x

g x = error (show x)

main :: IO (Either SomeException ())
main = try (evaluate (f ()))

