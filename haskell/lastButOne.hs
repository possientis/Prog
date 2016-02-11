lastButOne []       = error "list should have at least two elements"
lastButOne (x:[])   = error "list should have at least two elements"
lastButOne (x:y:[]) = x
lastButOne (x:xs)   = lastButOne xs 

