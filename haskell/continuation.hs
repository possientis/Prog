add :: Int -> Int -> Int 
add x y = x + y

sq :: Int -> Int
sq x  = x * x

pythagoras :: Int -> Int -> Int
pythagoras x y = add (sq x) (sq y)


-- cps: continuation passing style
sq_cps :: Int -> (Int -> r) -> r
sq_cps x = \k -> k (sq x)

add_cps :: Int -> Int -> (Int -> r) -> r
add_cps x y = \k -> k (add x y)

pythagoras_cps :: Int -> Int -> (Int -> r) -> r
pythagoras_cps x y = \k ->
  sq_cps x $ \x_sq ->
  sq_cps y $ \y_sq ->
  add_cps x_sq y_sq $ k

{-
 - Lemma: pythagoras_cps x y = \k -> k (pythagoras x y)
 -
 - Proof: pythogoras_cps x y k 
 -          = sq_cps x $ \x_sq -> sq_cps y $ \y_sq -> add_cps x_sq y_sq $ k 
 -          = (\x_sq -> sq_cps y $ \y_sq -> add_cps x_sq y_sq $ k) (sq x)
 -          = sq_cps y $ \y_sq -> add_cps (sq x) y_sq $ k
 -          = (\y_sq -> add_cps (sq x) y_sq $ k) (sq y)
 -          = add_cps (sq x) (sq y) $ k
 -          = add_cps (sq x) (sq y) k
 -          = k (add (sq x) (sq y)) 
 -          = k (pythagoras x y)
 -}        

-- thrice with no continuation
thrice :: (a -> a) -> a -> a
thrice f x = f (f (f x))


thrice_cps :: (a -> (a -> r) -> r) -> a -> (a -> r) -> r
thrice_cps f x k = (f x) $ \y -> (f y) $ \z -> (f z) $ k









