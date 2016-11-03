(load "main.scm")

; definition with 'analyze' leads to failure of subsequent lazy-eval
; no such failure occurs when strict definition is used

((analyze '(define (f x) (* x x))) global-env)    ; leads to failure

(define f-obj (strict-eval 'f))

(display "f = ")(display f-obj)(newline)

(define proc-thunk (lazy-eval 'f))
(define args (list (lazy-eval 5)))
(define proc (force-thunk proc-thunk)) 


; equivalent code
(lazy-apply-analyze-procedure proc args)

;(lazy-eval '(f 5))







