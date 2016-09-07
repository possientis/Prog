;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-analyze-procedure)) 
  (begin
    (define included-analyze-procedure #f)
    (display "loading analyze-procedure")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; testing
(define (analyze-procedure? procedure) (tagged-list? procedure 'analyze-procedure))

; making
(define (make-analyze-procedure parameters body env)
  (list 'analyze-procedure parameters body env))

; destructuring
(define (analyze-procedure-parameters procedure) (cadr procedure))
(define (analyze-procedure-body procedure) (caddr procedure))
(define (analyze-procedure-environment procedure) (cadddr procedure))

; apply
(define (apply-analyze-procedure proc args)
  (let ((body (analyze-procedure-body proc))
        (params (analyze-procedure-parameters proc))
        (init-env (analyze-procedure-environment proc)))
    (let ((extended-env ((init-env 'extended) params args)))
      (body extended-env))))

; lazy
; same code, but args is now expected to be a list of thunks
; and we are passing thunks as values in an extended environment
; and we are returning an evaluated thunk (environment is '()).

(define (lazy-apply-analyze-procedure proc args)
  (let ((body (analyze-procedure-body proc))
        (params (analyze-procedure-parameters proc))
        (init-env (analyze-procedure-environment proc)))
    (let ((extended-env ((init-env 'extended) params args)))
      (thunk (body extended-env) '()))))



))  ; include guard


