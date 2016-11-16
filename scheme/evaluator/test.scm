(load "main.scm")

(set-debug #f)

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

;(display "\n\nbody = ")(display body)(newline)(newline)
;(display "\n\nproc = ")(display proc)(newline)(newline)

(display "\n\n(force-thunk (lazy-eval '(f 5))) = ")
(let ((value (force-thunk (lazy-eval '(f 5)))))
  (display value)
  (if (thunk? value) 
    (begin
      (display ": -----> ")(display (force-thunk value)))))
(newline)(newline)

(display "\n\nequivalent code = ")
(let ((value (force-thunk (lazy-apply proc-thunk args))))
  (display value)
  (if (thunk? value) 
    (begin
      (display ": -----> ")(display (force-thunk value)))))
(newline)(newline)

; equivalent code
;(body env)


(exit 0)

#|
(eval-procedure 
  (env) 
  (begin 
    (analyze-apply (proc env) (map (lambda (x) (x env)) args))) 
  #<CLOSURE <anon> "environment1.scm": (m)>)
|#




