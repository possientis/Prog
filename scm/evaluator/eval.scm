(define (eval exp env)
  (cond ((self-evaluating? exp) exp)                            ; Ok
        ((variable? exp) (lookup-variable-value exp env))       ; Ok  TBI
        ((quoted? exp) (text-of-quotation exp))                 ; Ok  Ok
        ((assignment? exp) (eval-assignment exp env))           ; TBI Ok
        ((definition? exp) (eval-definition exp env))           ; TBI Ok
        ((if? exp) (eval-if exp env))                           ; TBI Ok
        ((lambda? exp)                                          ; TBI
         (make-procedure (lambda-parameters exp)                ; TBI TBI
                         (lambda-body exp)                      ; TBI
                         env))
        ((begin? exp) (eval-sequence (begin-actions exp) env))  ; TBI Ok  TBI 
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

; Even if we assume that we have knowledge of the fact that 
; 'first-operand' returns the left-most expression in a list,
; the implementation below does not make it clear whether
; our operands are evaluated from left to right, or from 
; right to left, since this will depend on the order of
; evaluation of the arguments to 'cons' in our implementation
; language.
(define (list-of-values exps env)
  (if (no-operands? exps)                                       ; TBI
    '()
    (cons (eval (first-operand exps) env)                       ; TBI
          (list-of-values (rest-operands exps) env))))          ; TBI

; evaluation from left to right
(define (list-of-values-LR exps env)
  (if (no-operands? exps)
    '()
    (let ((value (eval (first-operand exps) env)))
      (cons value (list-of-value (rest-operands exps) env)))))
; evaluation from right to left
(define (list-of-values-RL exps env)
  (if (no-operands? exps)
    '()
    (let ((rest (list-of-value (rest-operands exps) env)))
      (cons (eval (first-operand exps) env) rest))))


(define (eval-if exp env)
  (if (true? (eval (if-predicate exp) env))                     ; TBI
    (eval (if-consequent exp) env)                              ; TBI
    (eval (if-alternative exp) env)))                           ; TBI

(define (eval-sequence seq env)
  (cond ((last-exp? exps) (eval (first-exp exps) env))          ; TBI TBI
        (else (eval (first-exp exps) env)
              (eval-sequence (rest-exps exps) env))))           ; TBI

(define (eval-assignment exp env)
  (set-variable-value! (assignment-variable exp)                ; TBI TBI
                       (eval (assignement-value exp) env)       ; TBI
                       env)
  'ok)

(define (eval-definition exp env)
  (define-variable! (definition-variable exp)                   ; TBI TBI
                    (eval (definition-value exp) env)           ; TBI
                    env)
  'ok)

(define (self-evaluating? exp)
  (cond ((number? exp) #t)                                      
        ((string? exp) #t)                                      
        (else #f)))

(define (variable? exp) (symbol? exp))

(define (quoted? exp)
  (tagged-list? exp 'quote))                                    ; Ok

(define (text-of-quotation exp) (cadr exp))
(define (tagged-list? exp tag)
  (if (pair? exp)
    (eq? (car exp) tag)
    #f))



(define (true? value)
  ; TBI 
  #f)

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

(define (lookup-variable-value exp env)
  ; TBI
  0)

(define (assignment? exp)
  ; TBI
  #f)

(define (definition? exp)
  ; TBI
  #f)

(define (if? exp)
  ; TBI
  #f)

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



