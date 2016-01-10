(define (application? exp) (pair? exp)) ; need to be tested last

(define (apply procedure arguments)
  (cond ((primitive-procedure? procedure)                       ; TBI
         (apply-primitive-procedure procedure arguments))       ; TBI
        ((compound-procedure? procedure)                        ; TBI
         (eval-sequence
           (procedure-body procedure)                           ; TBI
           (extend-environment                                  ; TBI
             (procedure-parameters procedure)                   ; TBI
             arguments
             (procedure-environment procedure))))               ; TBI
        (else (error "Unknown procedure type -- APPLY" procedure))))


(define (operator exp) (car exp))

(define (operands exp) (cdr exp))

(define (list-of-values exps env)
  (if (no-operands? exps) '()
    (cons (eval (first-operand exps) env)                       
          (list-of-values (rest-operands exps) env))))      

(define (no-operands? exps) (null? exps))

(define (first-operand exps) (car exps))

(define (rest-operands exps) (cdr exps))

(define (eval-sequence seq env)
  (cond ((last-exp? exps) (eval (first-exp exps) env))          
        (else (eval (first-exp exps) env)
              (eval-sequence (rest-exps exps) env))))           

(define (last-exp? exps) (null? (cdr exps)))

(define (first-exp exps) (car exps))

(define (rest-exps exps) (cdr exps))


;-------------------------- NOT USED -------------------------------------------
; Even if we assume that we have knowledge of the fact that 
; 'first-operand' returns the left-most expression in a list,
; the implementation below does not make it clear whether
; our operands are evaluated from left to right, or from 
; right to left, since this will depend on the order of
; evaluation of the arguments to 'cons' in our implementation
; language.

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
;-------------------------------------------------------------------------------


