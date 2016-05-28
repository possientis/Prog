;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-definition)) 
  (begin
    (define included-definition #f)
    (display "loading definition")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 

(load "make.scm")

(define (definition-variable exp)
  (if (symbol? (cadr exp)) (cadr exp) (caadr exp)))

(define (definition-expression exp)
  (if (symbol? (cadr exp))
    (caddr exp)
    (make-lambda (cdadr exp)                                   
                 (cddr exp))))

(define (eval-definition exp env)
  ((env 'define!) (definition-variable exp)
                  (eval (definition-expression exp) env)))

; added for analyze
; the definition expression can be analyzed just once
(define (analyze-definition exp)
  (let ((var (definition-variable exp))
        (proc (definition-expression exp)))
    (let ((vproc (analyze proc)))
;      (newline)
;      (display "analyze-definition1: exp = ")(display exp)(newline)
;      (display "analyze-definition2: var = ")(display var)(newline)
;      (display "analyze-definition3: proc = ")(display proc)(newline)
;      (display "analyze-definition4: vproc = ")(display vproc)(newline)
      (lambda (env) ((env 'define!) var (vproc env)))))) 

))  ; include guard


