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

; strict apply
(define (strict-apply-primitive-procedure proc args)
  (let ((forced-args (map force-thunk args)))
    (apply (primitive-procedure-object proc) forced-args)))

; analyze apply
; We are calling force-thunk on the arguments prior to calling
; apply. This does not mean we expect the arguments to be thunks
; of course, but we accept this may happen due to the blurred
; semantics of the evaluator which mixes various modes of
; evaluation (strict, lazy, analyze). For example, if we were 
; to interpret the expression '(define (f x) (* x x)) in analyze 
; mode, the symbol 'f would be bound to an object of type 
; 'analyze-procedure' which would create a dependency to the 
; function 'analyze-apply-primitive-procedure' below. Now if 
; we were to evaluate an expression involving 'f in lazy
; mode, we may end up with thunks being passed to this function.

(define (analyze-apply-primitive-procedure proc args)
  (let ((forced-args (map force-thunk args)))
    (apply (primitive-procedure-object proc) forced-args))) 

; lazy
; proc is not expected to be of type thunk so no need to force it.
; args is expected to be a list of thunk which we need to force.
; the procedure returns an evaluated thunk, one for which environment is '().
(define (lazy-apply-primitive-procedure proc args)
  (make-thunk (apply (primitive-procedure-object proc) args) '()))
;  (let ((forced-args (map force-thunk args)))
;    (make-thunk (apply (primitive-procedure-object proc) forced-args) '())))

))  ; include guard



