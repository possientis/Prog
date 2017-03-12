(load "main.scm")

(newline)
(define (try a b) (if (= 0 a) 1 b))
(define (test) (display "test is running: "))
(display "result0 = ") (try 0 (test))(newline)

(strict-eval '(define (test) (display "test is running\n")))

(strict-eval '(define (try a b) (if (= 0 a) 1 b)))

(display "result1 = ")(display (force-thunk (lazy-eval '(try 0 (test)))))(newline)
(display "result1 = ")
(display (force-thunk (lazy-eval '(try 0 (display "no!!!")))))(newline)

(exit 0)
