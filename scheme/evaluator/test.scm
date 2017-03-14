(load "main.scm")

(strict-eval '(define (test) (display "test is running\n")))
(strict-eval '(define (try a b) (if (= 0 a) 1 b)))

; so far so good, test is not running, but what if we force thunk?
;(define t1 (lazy-eval '(try 0 (test))))
; still good, forcing and test is still not running
;(define v1 (force-thunk t1))

; wrong, display should not be running under lazy eval
;(define t2 (lazy-eval '(try 0 (display "This should not appear if lazy\n"))))

(define t3 (lazy-eval '(display "This should not appear\n")))

(exit 0)
