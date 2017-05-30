;(/ 1 0)


;(exit 0)

(catch 'numerical-overflow 
       (lambda () (display "oops, exception\n"))
       (lambda args 'ok)
       (lambda args 'ok))

