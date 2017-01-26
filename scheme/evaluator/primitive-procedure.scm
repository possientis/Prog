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
; In contrast to the 'analyze' case, we do not attempt to call
; force-thunks on the arguments prior to calling apply. We cannot
; say that the reason for this is very clear (the overall semantics
; of the evaluator mixing various modes of evaluation is rather
; complex) but we can think of at least two reasons. One reason is 
; that while the unit testing code succeeds when run by native scm, 
; it does lead to failure when run by the evaluator itself. Another
; reason is that forcing thunks would probably create circular depency: 
; force-thunk -> strict-eval -> strict-apply -> 
; strict-apply-primitive-procedure -> force-thunk

(define (strict-apply-primitive-procedure proc args)
  (apply (primitive-procedure-object proc) args))

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
  (let ((forced-args (map force-thunk args)))
    (debug "[DEBUG]: lazy-apply-primitive-procedure: proc = ")(debug proc)(debug-newline)
    (make-thunk (apply (primitive-procedure-object proc) forced-args) '())))

))  ; include guard



