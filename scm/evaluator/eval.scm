(define (eval exp env)
  (cond ((self-evaluating? exp) exp)                            
        ((variable? exp) (lookup-variable-value exp env))       ;TBI
        ((quoted? exp) (text-of-quotation exp))                 
        ((assignment? exp) (eval-assignment exp env))           
        ((definition? exp) (eval-definition exp env))           
        ((if? exp) (eval-if exp env))                           
        ((not? exp) (eval-not exp env))
        ((lambda? exp)                                          
         (make-procedure (lambda-parameters exp)               
                         (lambda-body exp)                      
                         env))
        ((begin? exp) (eval-sequence (begin-actions exp) env))  
        ((cond? exp) (eval (cond->if exp) env))              
        ((or? exp) (eval (or->if exp) env))
        ((and? exp) (eval (and->if exp) env))
        ((let? exp) (eval (let->combination exp) env))
        ((let*? exp) (eval (let*->nested-lets exp) env))
        ((application? exp)                                     
         (apply (eval (operator exp) env)                       
                (list-of-values (operands exp) env)))           
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
  (if (no-operands? exps)
    '()
    (cons (eval (first-operand exps) env)                       
          (list-of-values (rest-operands exps) env))))      

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
  (if (true? (eval (if-predicate exp) env))                     
    (eval (if-consequent exp) env)                             
    (eval (if-alternative exp) env)))                          

(define (eval-not exp env)
  (if (true? (eval (not-predicate exp) env))
    #f
    #t))  ;returning value #f ot #t rather than expression '#f or '#t

(define (true? value)
  (if value #t #f))

(define (eval-sequence seq env)
  (cond ((last-exp? exps) (eval (first-exp exps) env))          
        (else (eval (first-exp exps) env)
              (eval-sequence (rest-exps exps) env))))           

(define (eval-assignment exp env)
  (set-variable-value! (assignment-variable exp)                ; TBI Ok
                       (eval (assignement-value exp) env)       ; Ok 
                       env)
  'ok)

(define (eval-definition exp env)
  (define-variable! (definition-variable exp)                   ; TBI Ok 
                    (eval (definition-value exp) env)           
                    env)
  'ok)

(define (self-evaluating? exp)
  (cond ((number? exp) #t)                                      
        ((string? exp) #t)                                      
        (else #f)))

(define (variable? exp) (symbol? exp))

(define (quoted? exp)
  (tagged-list? exp 'quote))                                    

(define (text-of-quotation exp) (cadr exp))
(define (tagged-list? exp tag)
  (if (pair? exp)
    (eq? (car exp) tag)
    #f))

(define (assignment? exp)
  (tagged-list? exp 'set!))

(define (assignment-variable exp) (cadr exp))

(define (assignment-value exp) (caddr exp))

(define (definition? exp)
  (tagged-list? exp 'define))

(define (definition-variable exp)
  (if (symbol? (cadr exp))
    (cadr exp)
    (caadr exp)))

(define (definition-value exp)
  (if (symbol? (cadr exp))
    (caddr exp)
    (make-lambda (cdadr exp)                                   
                 (cddr exp))))
(define (lambda? exp) (tagged-list? exp 'lambda))

(define (lambda-parameters exp) (cadr exp))

(define (lambda-body exp) (cddr exp))

(define (make-lambda parameters body)
  (cons 'lambda (cons parameters body)))

(define (if? exp) (tagged-list? exp 'if))
(define (not? exp) (tagged-list? exp 'not))

(define (if-predicate exp) (cadr exp))
(define (not-predicate exp) (cadr exp))

(define (if-consequent exp) (caddr exp))

(define (if-alternative exp) 
  (if (not (null? (cdddr exp)))
    (cadddr exp)
    '#f)) ; returning symbol '#f, which will be evaluated as #f

(define (make-if predicate consequent alternative)
  (list 'if predicate consequent alternative))

(define (make-not predicate)
  (list 'not predicate))

(define (begin? exp) (tagged-list? exp 'begin)) 

(define (begin-actions exp) (cdr exp))

(define (last-exp? exps) (null? (cdr exps)))

(define (first-exp exps) (car exps))

(define (rest-exps exps) (cdr exps))

(define (sequence->exp exps)
  (cond ((null? exps) exps)
        ((last-exp? exps) (first-exp exps))
        (else (make-begin exps))))

(define (make-begin exps) (cons 'begin exps))

(define (application? exp) (pair? exp))

(define (operator exp) (car exp))

(define (operands exp) (cdr exp))

(define (no-operands? exps) (null? exps))

(define (first-operand exps) (car exps))

(define (rest-operands exps) (cdr exps))

(define (cond? exp) (tagged-list? exp 'cond))

(define (cond-clauses exp) (cdr exp))

(define (cond-else-clause? clause)
  (eq? (cond-predicate clause) 'else))

(define (cond-predicate clause) (car clause))

(define (cond-actions clause) (cdr clause))

(define (cond->if exp)
  (expand-clauses (cond-clauses exp)))

(define (expand-clauses clauses)
  (if (null? clauses)
    '#f ; returning symbol '#f which will be evaluated to #f
    (let ((first (car clauses))
          (rest (cdr clauses)))
      (if (cond-else-clause? first)
        (if (null? rest)
          (sequence->exp (cond-actions first))
          (error "ELSE clause isn't last -- COND->IF" clauses))
        (make-if (cond-predicate first)
                 (sequence->exp (cond-actions first))
                 (expand-clauses rest))))))

(define (or? exp) (tagged-list? exp 'or))
(define (and? exp) (tagged-list? exp 'and))
(define (or-predicates exp) (cdr exp))
(define (and-predicates exp) (cdr exp))

(define (or->if exp)
  (expand-or-predicates (or-predicates exp)))

(define (and->if exp)
  (expand-and-predicates (and-predicates exp)))

(define (expand-or-predicates predicates)
  (if (null? predicates)
    '#f ; returning symbol '#f which will be evaluated to #f
    (let ((first (car predicates))
          (rest (cdr predicates)))
      (if (null? rest)
        first
        (make-if first '#t (expand-or-predicates rest))))))

(define (expand-and-predicates predicates)
  (if (null? predicates)
    '#t ; returning symbol '#t which will be evaluated to #t
    (let ((first (car predicates))
          (rest (cdr predicates)))
      (if (null? rest)
        first
        (make-if (make-not first) '#f (expand-and-predicates rest))))))

(define (let? exp)
  (tagged-list? exp 'let))

(define (let-bindings exp)
  (cadr exp))

(define (let-body exp)
  (cddr exp))

(define (let-parameters exp)
  (map car (let-bindings exp)))

(define (let-operands exp)
  (map cadr (let-bindings exp)))

(define (let->combination exp)
  (cons (make-lambda (let-parameters exp) (let-body exp)) (let-operands exp)))

(define (let*? exp)
  (tagged-list? exp 'let*))

(define (let*-bindings exp)
  (cadr exp))

(define (let*-body exp)
  (cddr exp))

(define (make-let bindings body)
  (cons 'let (cons bindings body)))

(define (let*->nested-lets exp)
  (let ((bindings (let*-bindings exp)))
    (let-expand bindings (let*-body exp))))

(define (let-expand bindings body)
  (if (single-binding? bindings)
    (make-let bindings body)
    (make-let (car bindings)
              (let-expand (cdr bindings) body))))

(define (single-binding? binding)
  (null? (cdr binding)))

(define s '(let* ((x 3) (y (+ x 2)) (z (+ x y 5))) (* x z)))





