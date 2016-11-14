(load "main.scm")

; definition with 'analyze' leads to failure of subsequent lazy-eval
; no such failure occurs when strict definition is used

;(strict-eval '(define (f x) (* x x )) global-env)
;((analyze '(define (f x) (* x x))) global-env)    ; leads to failure
((analyze '(define (f x) x)) global-env)           ; no failure but ...


(define proc-thunk (lazy-eval 'f))
(define args (list (lazy-eval 5)))
(define proc (force-thunk proc-thunk)) 
(define body (analyze-procedure-body proc))
(define params (analyze-procedure-parameters proc))
(define env ((global-env 'extended) params args))

(display "\nbody = ")(display body)(newline)
(display "\nproc = ")(display proc)(newline)

(lazy-eval '(f 5) global-env)
; equivalent code
(body env)


;(display "\n\nresult = ")(display (force-thunk (lazy-eval '(f 5))))(newline)(newline)
;(display "\n\nresult = ")(display (force-thunk (body env)))(newline)(newline)


#|
(eval-procedure 
  (env) 
  (begin 
    (analyze-apply (proc env) (map (lambda (x) (x env)) args))) 
  #<CLOSURE <anon> "environment1.scm": (m)>)
|#




