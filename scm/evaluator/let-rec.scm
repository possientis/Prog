(load "make.scm")

(define (letrec-bindings exp) (cadr exp))
(define (letrec-body exp) (cddr exp))
(define (letrec-binding->define binding)
  (list 'define (car binding) (cadr binding)))
(define (letrec-define-list exp)
  (map letrec-binding->define (letrec-bindings exp)))

(define (letrec->combination exp)
  'TODO)
