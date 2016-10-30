(load "main.scm")

; definition with 'analyze' leads to failure of subsequent lazy-eval
; no such failure occurs when strict definition is used

((analyze '(define (f x) (* x x))) global-env)    ; leads to failure

;(strict-eval '(define (f x) (* x x)) global-env)  ; no issues there



(display (strict-eval '(f 5)))(newline) ; succeeds regardless of definition type

(display (force-thunk (lazy-eval '(f 5)))) (newline) ; fails if analytic definition




