;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-self-evaluating)) 
  (begin
    (define included-self-evaluating #f)
    (display "loading self-evaluating")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 

; eval
(define (eval-self-evaluating exp env) exp)

; analyze
(define (analyze-self-evaluating exp) (lambda (env) exp)) 


))  ; include guard
