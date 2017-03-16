(define (try a b) 
  (display "try is running\n")
  (if (= 0 a) 'ok b))

(define (test) (display "test is running\n"))

(try 0 (test))

(exit 0)


