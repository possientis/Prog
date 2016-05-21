;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-not)) 
  (begin
    (define included-not #f)
    (display "loading not")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 

(load "true-false.scm")

(define (not-predicate exp) (cadr exp))

(define (eval-not exp env)
  (if (true? (eval (not-predicate exp) env)) #f #t))  

; added for analyze
(define (analyze-not exp)
  (let ((pproc (analyze (not-predicate exp))))
    (lambda (env)
      (if (true? (pproc env)) #f #t))))

))  ; include guard


