(load "main.scm")

(strict-eval '(define (test)
                (display "test is running\n")))

(strict-eval '(define (try a)
                (display "try is running\n") #t))

(define t (lazy-eval '(try (test))))

(define s (make-thunk '(try (test)) global-env))

(force-thunk s) ; HERE !!!!!! doing strict eval when forcing -> wrong semantics


#|
(define (test) 
  (display "test is running\n"))


(define (try a) 
  (display "try is running\n") #t)


(display (try (test)))

|#

(exit 0)


