(define (eval exp env)
  (cond ((self-evaluating? exp) exp)
        ((variable? exp) (lookup-variable-value exp env))
        ((quoted? exp) (text-of-quotation exp))
        ((assignment? exp) (eval-assignment exp env))
        ((definition? exp) (eval-definition exp env))
      

(define (self-evaluating? exp)
  ; TBI
  #t)

(define (variable? exp)
  ; TBI
  #f)

(define (lookup-variable-value exp env)
  ; TBI
  0)

(define (quoted? exp)
  ; TBI
  #f)

(define (text-of-quotation exp)
  ; TBI
  "")

(define (assignment? exp)
  ; TBI
  #f)

(define (eval-assignment exp env)
  ; TBI
  'ok)

(define (definition? exp)
  ; TBI
  #f)

(define (eval-definition exp env)
  ; TBI
  'ok)

