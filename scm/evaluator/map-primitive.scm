;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-map-primitive)) 
  (begin
    (define included-map-primitive #f)
    (display "loading map-primitive")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 


(define (map-primitive procedure seq) ; quick and dirty, one dimension
  (cond ((null? seq) '())
        (else 
;          (display "arg = ")(display (car seq))(newline)
          (cons (apply procedure (list (car seq))) 
                    (map-primitive procedure (cdr seq))))))



;(display (map + '(1 2 3) '(4 5 6)))(newline)


))  ; include guard
