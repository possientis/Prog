(load "main.scm")

(lazy-eval '(define (try a b) (if (= 0 a) 1 b)))
(lazy-eval '(define (test) (display "+++test is running+++") 2))


;(lazy-eval '(try 0 (test)))

(display (lazy-eval '(test)))(newline)


(exit 0)
