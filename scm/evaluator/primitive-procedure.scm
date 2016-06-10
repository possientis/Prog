;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-primitive-procedure)) 
  (begin
    (define included-primitive-procedure #f)
    (display "loading primitive-procedure")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(load "apply-in-underlying-scheme.scm")
(load "tagged-list.scm")

; testing
(define (primitive-procedure? proc) (tagged-list? proc 'primitive-procedure))

; making
(define (make-primitive-procedure object)
  (list 'primitive-procedure object))

; destructuring
(define (primitive-procedure-object proc) (cadr proc))

; applying
(define (apply-primitive-procedure proc args)
  (apply-in-underlying-scheme (primitive-procedure-object proc) args)) 

))  ; include guard



