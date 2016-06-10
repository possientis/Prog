;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-analyze-procedure)) 
  (begin
    (define included-analyze-procedure #f)
    (display "loading analyze-procedure")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(load "tagged-list.scm")

; testing
(define (analyze-procedure? procedure) (tagged-list? procedure 'analyze-procedure))

; making
(define (make-analyze-procedure parameters body env)
  (list 'analyze-procedure parameters body env))

; destructuring
(define (analyze-procedure-parameters procedure) (cadr procedure))
(define (analyze-procedure-body procedure) (caddr procedure))
(define (analyze-procedure-environment procedure) (cadddr procedure))

; applying
(define (apply-analyze-procedure proc args)
  (let ((body (analyze-procedure-body proc))
        (params (analyze-procedure-parameters proc))
        (init-env (analyze-procedure-environment proc)))
    (let ((extended-env ((init-env 'extended) params args)))
      (body extended-env))))

))  ; include guard


