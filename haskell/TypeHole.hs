data List a = Nil | Cons a (List a)

instance Functor List where
    fmap f (Cons x xs) = Cons (f x) (fmap f _) -- type hole

main :: IO ()
main = return ()

