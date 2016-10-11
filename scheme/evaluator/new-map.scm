;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-new-map)) 
  (begin
    (define included-new-map #f)
    (display "loading new-map")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 

; TODO: provide a multi-dimensional implementation
(define (new-map procedure seq)
  (cond ((null? seq) '())
        (else 
          (cons (new-apply procedure (list (car seq))) 
                    (new-map procedure (cdr seq))))))


))  ; include guard
