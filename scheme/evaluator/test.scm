(load "main.scm")

;(strict-eval '(define (try a b)
;                (display "try is running\n")
;                (if (= 0 a) 'ok b)))
;(strict-eval '(define (test) (display "test is running\n")))

;(force-thunk (lazy-eval '(try 0 (test))))

(define code (filename->code "test1.scm"))
(display code)(newline)

; (begin (define (try a b) 
;          (display "try is running") 
;          (if (= 0 a) 'ok b)) 
;          (define (test) (display "test is running")) 
;          (try 0 (test)) 
;          (exit 0))

(define t (lazy-eval code))

(force-thunk t)

(exit 0)
