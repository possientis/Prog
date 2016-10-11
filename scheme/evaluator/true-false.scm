;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-true-false)) 
  (begin
    (define included-true-false #f)
    (display "loading true-false")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 

(define (true? value)
  (not (eq? value #f))) 

(define (false? value)
   (eq? value #f))

))  ; include guard

