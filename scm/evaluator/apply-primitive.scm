;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-apply-primitive)) 
  (begin
    (define included-apply-primitive #f)
    (display "loading apply-primitive")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 


(define (apply-primitive procedure arguments)
  (apply procedure arguments))


))  ; include guard
