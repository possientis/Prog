(load "make.scm")
(define (letrec-bindings exp) (cadr exp))
(define (letrec-body exp) (cddr exp))
(define (letrec-binding->define binding)
  (list 'define (car binding) (cadr binding)))
(define (letrec-define-list exp)
  (map letrec-binding->define (letrec-bindings exp)))
(define (letrec-new-body exp)
  (append (letrec-define-list exp) (letrec-body exp)))

(define (letrec->combination exp)
  (list (make-lambda '() (letrec-new-body exp))))


;(define expr '(letrec ((x1 a1)(x2 a2)) (cond ((eq? x1 x2) 1) (else 2))))
;(display "expr        = ")(display expr)(newline)
;(display "bindings    = ")(display (letrec-bindings expr))(newline)
;(display "body        = ")(display (letrec-body expr))(newline) 
;(display "define list = ")(display (letrec-define-list expr))(newline)
;(display "new body    = ")(display (letrec-new-body expr))(newline)
;(display "new code    = ")(display (letrec->combination expr))(newline)

; expr = (letrec ((x1 a1) (x2 a2)) (cond ((eq? x1 x2) 1) (else 2)))
;
; generated code is not a lambda expression (lambda () ... ). It is a lambda
; expression which is being called ((lambda () ... ))
; ((lambda () (define x1 a1) (define x2 a2) (cond ((eq? x1 x2) 1) (else 2))))

