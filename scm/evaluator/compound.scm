;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-compound)) 
  (begin
    (define included-compound #f)
    (display "loading compound")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 

(define (procedure-parameters procedure) (cadr procedure))

(define (procedure-body procedure) (caddr procedure))

(define (procedure-environment procedure) (cadddr procedure))


))  ; include guard

