module  Formula 
  ( Formula(..)
  , belong
  , bot
  , imply
  , forAll
  ) where


data Formula v  
  = Belong v v
  | Bot
  | Imply (Formula v) (Formula v)
  | Forall v (Formula v)
  deriving (Eq, Ord)

belong = Belong
bot = Bot
imply = Imply
forAll = Forall

fold :: (v -> v -> b) -> b -> (b -> b -> b) -> (v -> b -> b) -> Formula v -> b
fold  fbelong fbot fimply fforAll = f where
  f (Belong x y)  = fbelong x y
  f (Bot)         = fbot
  f (Imply p q)   = fimply (f p) (f q)
  f (Forall x p)  = fforAll x (f p)

instance (Show v) => Show (Formula v) where
  show = fold fbelong fbot fimply fforAll where
    fbelong x y = (show x) ++ ":" ++ (show y)
    fbot        = "!"
    fimply s t  = "(" ++ s ++ " -> " ++ t ++ ")"
    fforAll x s = "A" ++ (show x) ++ "." ++ s

instance Functor Formula where
  fmap f  = fold fbelong fbot fimply fforAll where
    fbelong x y = belong (f x) (f y)
    fbot        = bot
    fimply p q  = imply p q
    fforAll x p = forAll (f x) p

