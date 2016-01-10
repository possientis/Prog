(define (eval exp env)
  (cond ((self-evaluating? exp) exp)                            
        ((variable? exp) (lookup-variable-value exp env))       ;TBI
        ((quoted? exp) (text-of-quotation exp))                 
        ((assignment? exp) (eval-assignment exp env))           
        ((definition? exp) (eval-definition exp env))           
        ((if? exp) (eval-if exp env))                           
        ((not? exp) (eval-not exp env))
        ((lambda? exp)(make-procedure(lambda-params exp)(lambda-body exp)env))
        ((begin? exp) (eval-sequence (begin-actions exp) env))  
        ((cond? exp) (eval (cond->if exp) env))              
        ((or? exp) (eval (or->if exp) env))
        ((and? exp) (eval (and->if exp) env))
        ((let? exp) (eval (let->combination exp) env))
        ((named-let? exp) (eval (named-let->combination exp) env))
        ((let*? exp) (eval (let*->nested-lets exp) env))
        ((application? exp)(apply (eval (operator exp) env)
                                  (list-of-values (operands exp) env)))           
        (else  (error "Unknown expression type -- EVAL" exp))))
        
(define (eval-if exp env)
  (if (true? (eval (if-predicate exp) env))                     
    (eval (if-consequent exp) env)                             
    (eval (if-alternative exp) env)))                          

(define (eval-not exp env)
  (if (true? (eval (not-predicate exp) env))
    #f
    #t))  ;returning value #f ot #t rather than expression '#f or '#t

(define (true? value)
  (not (eq? #f))) 

(define (false? value)
   (eq? #f))

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
  (if (pair? exp) (eq? (car exp) tag) #f))

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

(define (lambda-params exp) (cadr exp))

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

(define (make-not predicate)
  (list 'not predicate))

(define (begin? exp) (tagged-list? exp 'begin)) 

(define (begin-actions exp) (cdr exp))

(define (make-begin exps) (cons 'begin exps))

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

(define (named-let? exp)
  (and (tagged-list? exp 'let) (symbol? (cadr exp))))

(define (named-let-variable exp)
  (cadr exp))

(define (let? exp)
  (and (tagged-list? exp 'let) (not (symbol? (cadr exp)))))

(define (let-bindings exp)
  (cadr exp))

(define (named-let-bindings exp)
  (caddr exp))

(define (let-body exp)
  (cddr exp))

(define (named-let-body exp)
  (cdddr exp))

(define (let-parameters exp)
  (map car (let-bindings exp)))

(define (named-let-parameters exp)
  (map car (named-let-bindings exp)))

(define (let-operands exp)
  (map cadr (let-bindings exp)))

(define (named-let-operands exp)
  (map cadr (named-let-bindings exp)))

(define (named-let-function exp)
  (make-lambda (named-let-parameters exp) (named-let-body exp)))

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
    (make-let (list (car bindings))
              (list (let-expand (cdr bindings) body)))))

(define (single-binding? binding)
  (null? (cdr binding)))

(define (named-let-definition exp)
  (list 'define (named-let-variable exp) (named-let-function exp)))

(define (named-let-function-call exp)
  (cons (named-let-variable exp) (named-let-parameters exp)))

(define (named-let->combination exp)
  (cons (make-lambda (named-let-parameters exp) 
                     (list (named-let-definition exp) 
                           (named-let-function-call exp))) 
        (named-let-operands exp)))

(define s '(let loop ((x 10) (a 0)) (if (= x 0) a (loop (- x 1) (+ x a)))))
