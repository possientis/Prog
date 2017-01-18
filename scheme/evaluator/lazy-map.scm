;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-lazy-map)) 
  (begin
    (define included-lazy-map #f)
    (display "loading lazy-map")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 

; TODO: provide a multi-dimensional implementation
(define (lazy-map procedure seq)
  (cond ((null? seq) '())
        (else 
          (cons (lazy-apply procedure (list (car seq))) 
                    (lazy-map procedure (cdr seq))))))


))  ; include guard
