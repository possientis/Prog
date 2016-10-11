(load "connector.scm")

(define (cf-converter c f)
  (let ((u (connector))
        (v (connector))
        (w (connector))
        (x (connector))
        (y (connector)))
    (multiplier c w u)
    (multiplier v x u)
    (adder v y f)
    (constant 9 w)
    (constant 5 x)
    (constant 32 y)
    'ok))

(define C (connector))
(define F (connector))

(cf-converter C F)
(probe "Celsius temp" C)
(probe "Fahrenheit temp" F)



((C 'set-value!) 25 'user)
((F 'set-value!) 212 'user) ; should create a contradiction
((C 'forget-value!) 'user)
((F 'set-value!) 212 'user) ; no longer a contradiction
((F 'forget-value!) 'user)

