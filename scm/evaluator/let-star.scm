(load "make.scm") ; make-let

(define (let*-bindings exp) (cadr exp))
(define (let*-body exp) (cddr exp))
(define (single-binding? binding) (null? (cdr binding)))

(define (let*->nested-lets exp)
  (let ((bindings (let*-bindings exp)))
    (let-expand bindings (let*-body exp))))

(define (let-expand bindings body)
  (if (single-binding? bindings)
    (make-let bindings body)
    (make-let (list (car bindings))
              (list (let-expand (cdr bindings) body)))))

