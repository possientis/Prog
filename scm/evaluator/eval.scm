(define (eval exp env)
  (cond ((self-evaluating? exp) exp)                            ; TBI
        ((variable? exp) (lookup-variable-value exp env))       ; TBI TBI
        ((quoted? exp) (text-of-quotation exp))                 ; TBI TBI
        ((assignment? exp) (eval-assignment exp env))           ; TBI TBI
        ((definition? exp) (eval-definition exp env))           ; TBI TBI
        ((if? exp) (eval-if exp env))                           ; TBI TBI
        ((lambda? exp)                                          ; TBI
         (make-procedure (lambda-parameters exp)                ; TBI TBI
                         (lambda-body exp)                      ; TBI
                         env))
        ((begin? exp) (eval-sequence (begin-actions exp) env))  ; TBI TBI TBI 
        ((cond? exp) (eval (cond->if exp) env))                 ; TBI TBI
        ((application? exp)                                     ; TBI 
         (apply (eval (operator exp) env)                       ; Ok  TBI
                (list-of-values (operands exp) env)))           ; Ok  TBI 
        (else  (error "Unknown expression type -- EVAL" exp))))
        
(define (apply procedure arguments)
  (cond ((primitive-procedure? procedure)                       ; TBI
         (apply-primitive-procedure procedure arguments))       ; TBI
        ((compound-procedure? procedure)                        ; TBI
         (eval-sequence
           (procedure-body procedure)                           ; TBI
           (extend-environment                                  ; TBI
             (procedure-parameters procedures)                  ; TBI
             arguments
             (procedure-environment procedure))))               ; TBI
        (else (error "Unknown procedure type -- APPLY" procedure))))

(define (list-of-values exps env)
  (if (no-operands? exps)
    '()
    (cons (eval (first-operand exps) env)
          (list-of-values (rest-operands exps) env))))




(define (primitive-procedure? procedure)
  ; TBI
  #t)

(define (compound-procedure? procedure)
  ; TBI
  #f)

(define (apply-primitive-procedure procedure arguments)
  ; TBI
  'ok)

(define (procedure-body procedure)
  ; TBI
  'ok)

(define (procedure-parameters procedure)
  ; TBI
  'ok)

(define (extend-environment params arguments env)
  ; TBI
  'ok)

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

(define (if? exp)
  ; TBI
  #f)

(define (eval-if exp env)
  ; TBI
  'ok)

(define (lambda? exp)
  ; TBI
  #f)

(define (make-procedure params body env)
  ; TBI
  'ok)

(define (lambda-parameters exp)
  ; TBI
  'ok)

(define (lambda-body exp)
  ; TBI
  'ok)

(define (begin? exp)
  ; TBI
  #f)

(define (eval-sequence seq env)
  ; TBI
  'ok)

(define (begin-actions exp)
  ; TBI
  '())

(define (cond->if exp)
  ; TBI
  'ok)

(define (operator exp)
  ; TBI
  'ok)

(define (operands exp)
  ; TBI
  'ok)



