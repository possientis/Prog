data Free f a = Pure a | Free (f (Free f a))

ex1 :: Free f ()
ex1  = Pure ()




