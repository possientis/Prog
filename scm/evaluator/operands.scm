;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-operands)) 
  (begin
    (define included-operands #f)
    (display "loading operands")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 


(define (list-of-values operands env)
  (if (no-operands? operands) '()
    (cons (eval (first-operand operands) env)                       
          (list-of-values (rest-operands operands) env))))      

(define (no-operands? operands) (null? operands))

(define (first-operand operands) (car operands))

(define (rest-operands operands) (cdr operands))

(define (last-operand? operands) (null? (cdr operands)))

(define (eval-sequence operands env)
  (cond ((last-operand? operands) (eval (first-operand operands) env))          
        (else (eval (first-operand operands) env)
              (eval-sequence (rest-operands operands) env))))           

; added for analyze
(define (analyze-sequence operands)
  (define (sequentially proc1 proc2)
    (lambda (env) (proc1 env) (proc2 env)))
  (define (loop first-proc rest-procs)
    (if (null? rest-procs)
      first-proc
      (loop (sequentially first-proc (car rest-procs))
            (cdr rest-procs))))
  (let ((procs (map analyze exps)))
    (if (null? procs) (error "Empty sequence -- ANALYSE"))
    (loop (car procs) (cdr procs))))

)) ; include guard




