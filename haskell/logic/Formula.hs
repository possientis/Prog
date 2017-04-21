module  Formula 
      ( Formula(..)
      , FirstOrder
      , belong
      , bot
      , imply
      , forall
      , toFormula
      , fromFormula
      ) where



class FirstOrder m where
  belong      :: v -> v -> m v
  bot         :: m v
  imply       :: m v -> m v -> m v
  forall      :: v -> m v -> m v
  toFormula   :: m v -> Formula v
  fromFormula :: Formula v -> m v


data Formula v  = Belong v v
                | Bot
                | Imply (Formula v) (Formula v)
                | Forall v (Formula v)

instance FirstOrder Formula where
  belong      = Belong
  bot         = Bot
  imply       = Imply
  forall      = Forall 
  toFormula   = id
  fromFormula = id
  

