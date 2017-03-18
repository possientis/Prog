(load "main.scm")

;(strict-eval '(define (try a b)
;                (display "try is running\n")
;                (if (= 0 a) 'ok b)))
;(strict-eval '(define (test) (display "test is running\n")))

;(force-thunk (lazy-eval '(try 0 (test))))

;(define code (filename->code "test1.scm"))
;(display code)(newline)

; (begin (define (try a b) 
;          (display "try is running") 
;          (if (= 0 a) 'ok b)) 
;          (define (test) (display "test is running")) 
;          (try 0 (test)) 
;          (exit 0))

(define code '(begin
                 (define (try a b)
                   (display "try is running\n")
                   (if (= 0 a) 'ok b))
                 (define (test) (display "test is running\n"))
                 (try 0 (test))))


(define code1 '(define (try a b)
                 (display "try is running\n")
                  (if (= 0 a) 'ok b)))
(define code2 '(define (test) (display "test is running\n")))
(define code3 '(try 0 (test)))
(define code4 '(exit 0))


(define t1 (lazy-eval code1))
;(force-thunk t1)
(define t2 (lazy-eval code2))
;(force-thunk t2)
(define t3 (lazy-eval code3))
;(force-thunk t3)

(define t (lazy-eval code))
(force-thunk t)

(exit 0)
