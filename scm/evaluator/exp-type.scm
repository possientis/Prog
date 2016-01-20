(define (tagged-list? exp tag) (if (pair? exp) (eq? (car exp) tag) #f))

(define (self-evaluating? exp) 
  (cond ((number? exp) #t)
        ((string? exp) #t)
        ((eq? #t exp) #t)
        ((eq? #f exp) #t)
        (else #f)))

(define (variable? exp) (symbol? exp))

(define (quoted? exp) (tagged-list? exp 'quote))                                    

(define (assignment? exp) (tagged-list? exp 'set!))

(define (definition? exp) (tagged-list? exp 'define))

(define (if? exp) (tagged-list? exp 'if))

(define (not? exp) (tagged-list? exp 'not))

(define (lambda? exp) (tagged-list? exp 'lambda))

(define (begin? exp) (tagged-list? exp 'begin)) 

(define (cond? exp) (tagged-list? exp 'cond))

(define (or? exp) (tagged-list? exp 'or))

(define (and? exp) (tagged-list? exp 'and))

(define (let? exp) (and (tagged-list? exp 'let) (not (symbol? (cadr exp))))) 

(define (named-let? exp) (and (tagged-list? exp 'let) (symbol? (cadr exp)))) 

(define (let*? exp) (tagged-list? exp 'let*))

(define (application? exp) (pair? exp)) ; need to be tested last

