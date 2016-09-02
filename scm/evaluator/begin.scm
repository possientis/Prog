;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-begin)) 
  (begin
    (define included-begin #f)
    (display "loading begin")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 

; The evaluation or analysis of a begin expression is all about the evaluation
; or analysis of a sequence of expressions. As far as the returned value is 
; concerned, only the last expression of the sequence matters. However, this
; does not mean that the other expressions of the sequence should be ignored,
; as these may carry side effects. So we should not forget to evaluate every
; expression, (and eveluate it just once so as to avoid duplicate side-effect).

; testing
(define (begin? exp) (tagged-list? exp 'begin)) 

; making
(define (make-begin operands) (cons 'begin operands))

; destructuring
(define (begin-actions exp) (cdr exp))

; eval
(define (eval-begin exp env)
  (let ((actions (begin-actions exp)))
    (eval-sequence actions env)))

; analyze
(define (analyze-begin exp)
  (let ((actions (begin-actions exp)))
    (analyze-sequence actions)))

; lazy
(define (lazy-eval-begin exp env)
  (let ((actions (begin-actions exp)))
    (lazy-eval-sequence actions env)))

; eval
(define (eval-sequence operands env)
  (if (null? operands)
    unspecified-value 
    (let ((first (new-eval (car operands) env)))  ; side effects now
      (if (null? (cdr operands))
        first
        (eval-sequence (cdr operands) env))))); don't re-evaluate first

; analyze
(define (analyze-sequence operands)
  (if (null? operands)
    (lambda (env) unspecified-value)
    (let ((first (analyze (car operands))))
      (if (null? (cdr operands))
        first
        (let ((rest (analyze-sequence (cdr operands))))
          (lambda (env) (first env) (rest env))))))) ; 'first' for side-effects

; lazy
(define (lazy-eval-sequence operands env)
  (if (null? operands)
    (thunk unspecified-value '())
    (let ((first (lazy-eval (car operands) env)))
      (if (null? (cdr operands))
        first
        (lazy-eval-sequence (cdr operands) env)))));

))  ; include guard




