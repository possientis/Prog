;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-map-primitive)) 
  (begin
    (define included-map-primitive #f)
    (display "loading map-primitive")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 


(define (map-primitive procedure seq) ; quick and dirty, one dimension, temporary
  (cond ((null? seq) '())
        (else 
          (cons (new-apply procedure (list (car seq))) 
                    (map-primitive procedure (cdr seq))))))


))  ; include guard
