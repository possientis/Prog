;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-primitive-procedure)) 
  (begin
    (define included-primitive-procedure #f)
    (display "loading primitive-procedure")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; testing
(define (primitive-procedure? proc) (tagged-list? proc 'primitive-procedure))

; making
(define (make-primitive-procedure object)
  (list 'primitive-procedure object))

; destructuring
(define (primitive-procedure-object proc) (cadr proc))

; apply
(define (apply-primitive-procedure proc args)
  (apply (primitive-procedure-object proc) args)) 

; lazy
; proc is not expected to be of type thunk so no need to force it.
; args is expected to be a list of thunk which we need to force.
; the procedure returns an evaluated thunk, one for which environment is '().
(define (lazy-apply-primitive-procedure proc args)
  (let ((forced-args (map (lambda (thunk) (thunk 'value)) args)))
    (thunk (apply (primitive-procedure-object proc) forced-args) '())))

))  ; include guard



