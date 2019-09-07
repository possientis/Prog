data Matter = Liquid | Solid 

Eq Matter where
  (==) Liquid Liquid = True
  (==) Solid  Solid  = True
  (==) _      _      = False 

data X : Type where
  MkX : (a : Int) -> (b : Double) -> X
