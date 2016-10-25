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

; apply (deprecated)
(define (apply-eval-procedure proc args)
  (display "check2: apply-eval is deprecated ...")(newline)
  (let ((body (eval-procedure-body proc))
        (params (eval-procedure-parameters proc))
        (init-env (eval-procedure-environment proc)))
    (let ((extended-env ((init-env 'extended) params args)))
      (new-eval body extended-env))))

; strict apply
(define (strict-apply-eval-procedure proc args)
  (let ((body (eval-procedure-body proc))
        (params (eval-procedure-parameters proc))
        (init-env (eval-procedure-environment proc)))
    (let ((extended-env ((init-env 'extended) params args)))
      (strict-eval body extended-env))))

; analyze apply
(define (analyze-apply-eval-procedure proc args)
  (let ((body (eval-procedure-body proc))
        (params (eval-procedure-parameters proc))
        (init-env (eval-procedure-environment proc)))
    (let ((extended-env ((init-env 'extended) params args)))
      ((analyze body) extended-env))))


; lazy apply
; proc is not expected to be a thunk so we do not force it
; args is expected to be a list of thunks. However contrary 
; to the case of primitive procedure, we do not force them 
; either. Instead, we pass them directly as values to construct
; an extended environment, from which we return a new thunk.
(define (lazy-apply-eval-procedure proc args)
  (let ((body (eval-procedure-body proc))
        (params (eval-procedure-parameters proc))
        (init-env (eval-procedure-environment proc)))
    (let ((extended-env ((init-env 'extended) params args)))
      (lazy-eval body extended-env))))

))  ; include guard
