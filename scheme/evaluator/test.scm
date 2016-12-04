(load "main.scm")

(set-debug #t)

(strict-eval '(define f (lambda args args)))

(define proc (strict-eval 'f))
(newline)
(display "proc = ")(display proc)(newline)
(define params (eval-procedure-parameters proc))
(display "params = ")(display params)(newline)
(define body (eval-procedure-body proc))
(display "body = ")(display body)(newline)

; same as proc
(define evalp (make-eval-procedure 'args (list 'begin 'args) global-env))
;(display "evalp = ")(display evalp)(newline)


(define func (lambda arg (begin arg)))
;(display "(func 0) = ")(display (func 0))(newline)
;(display "(apply func '(0)) = ")(display (apply func '(0)))(newline)


;(display "\nstrict:\n")
;(display "(strict-apply proc '(0)) = ")(display (strict-apply proc '(0)))(newline)
;(display "(strict-eval '(f 0)) = ")(display (strict-eval '(f 0)))(newline)

;(display "\nlazy:\n")
;(define v (lazy-apply proc '(0)))
;(display "(force-thunk (lazy-apply proc '(0))) = ")
;(display (force-thunk v))(newline)


(define w (lazy-eval '(f 0)))
(define y (force-thunk w))
(define z (map force-thunk y))  ; needed to get expected result !!

(display "\n(force-thunk (lazy-eval '(f 0))) = ")(display y)(newline)

;(display z)(newline)


(exit 0)
