;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-strict-map)) 
  (begin
    (define included-strict-map #f)
    (display "loading strict-map")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 

; TODO: provide a multi-dimensional implementation
(define (strict-map procedure seq)
  (cond ((null? seq) '())
        (else 
          (cons (strict-apply procedure (list (car seq))) 
                    (strict-map procedure (cdr seq))))))


))  ; include guard
