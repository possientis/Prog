;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-lambda)) 
  (begin
    (define included-lambda #f)
    (display "loading lambda")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 

(load "make.scm")
(load "operands.scm")

(define (lambda-params exp) (cadr exp))

(define (lambda-body exp) (cddr exp))

; added for analyze
; important gain in efficiency as we analyze the body just once
(define (analyze-lambda exp)
  (let ((vars (lambda-params exp))
        (bproc (analyze-sequence (lambda-body exp))))
    (lambda (env)
      (make-procedure vars bproc env))))

))  ; include guard

