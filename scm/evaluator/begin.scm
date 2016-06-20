;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-begin)) 
  (begin
    (define included-begin #f)
    (display "loading begin")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 

(load "tagged-list.scm")
(load "unspecified.scm")

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


(define (eval-sequence operands env)
  (if (null? operands)
    unspecified-value 
    (let ((first (eval (car operands) env)))
      (if (null? (cdr operands))
        first
        (eval-sequence (cdr operands) env)))))


; added for analyze
(define (analyze-sequence operands)
  (define (sequentially proc1 proc2)
    (lambda (env) (proc1 env) (proc2 env)))
  (define (loop first-proc rest-procs)
    (if (null? rest-procs)
      first-proc
      (loop (sequentially first-proc (car rest-procs))
            (cdr rest-procs))))
  (let ((procs (map analyze operands)))
    (if (null? procs) (error "Empty sequence -- ANALYSE"))
    (loop (car procs) (cdr procs))))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



))  ; include guard




