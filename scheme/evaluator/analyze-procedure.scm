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


; strict apply
(define (strict-apply-analyze-procedure proc args)
  (let ((body (analyze-procedure-body proc))
        (params (analyze-procedure-parameters proc))
        (init-env (analyze-procedure-environment proc)))
    (let ((extended-env ((init-env 'extended) params args)))
      (body extended-env))))


; analyze apply (same code as strict)
(define (analyze-apply-analyze-procedure proc args)
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
  (display "\ncheck9: proc = ")(display proc)(newline)
  (display "\ncheck10: args = ")(display args)(newline)
  (let ((body (analyze-procedure-body proc))
        (params (analyze-procedure-parameters proc))
        (init-env (analyze-procedure-environment proc)))
    (display "\ncheck11: body = ")(display body)(newline)
    (display "\ncheck12: params = ")(display params)(newline)
    (let ((extended-env ((init-env 'extended) params args)))
      (display "\ncheck13: in env (force-thunk x) = ")
        (display (force-thunk (strict-eval 'x extended-env)))(newline)
        (display "\ncheck14: (body env) = ")(display (body extended-env))(newline)
      (make-thunk (body extended-env) '()))))


))  ; include guard


