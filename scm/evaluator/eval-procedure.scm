;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-eval-procedure)) 
  (begin
    (define included-eval-procedure #f)
    (display "loading eval-procedure")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; testing
(define (eval-procedure? procedure) (tagged-list? procedure 'eval-procedure))

; making
(define (make-eval-procedure parameters body env) 
  (list 'eval-procedure parameters body env))

; destructuring
(define (eval-procedure-parameters procedure) (cadr procedure))
(define (eval-procedure-body procedure) (caddr procedure))
(define (eval-procedure-environment procedure) (cadddr procedure))

; applying
(define (apply-eval-procedure proc args)
  (let ((body (eval-procedure-body proc))
        (params (eval-procedure-parameters proc))
        (init-env (eval-procedure-environment proc)))
    (let ((extended-env ((init-env 'extended) params args)))
      (new-eval body extended-env))))

))  ; include guard
