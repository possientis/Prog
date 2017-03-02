(define (test) (display "+++ test is running +++\n"))

(define (try a b) (if (= 0 a) 1 b))

(display "trying out ...\n")
(try 0 (test))  ; 'test' should not run under lazy eval
(display "attempt is now complete \n")

(exit 0)
