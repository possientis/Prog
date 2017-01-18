;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; include guard ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(if (not (defined? included-analyze-map)) 
  (begin
    (define included-analyze-map #f)
    (display "loading analyze-map")(newline)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 

; TODO: provide a multi-dimensional implementation
(define (analyze-map procedure seq)
  (cond ((null? seq) '())
        (else 
          (cons (analyze-apply procedure (list (car seq))) 
                    (analyze-map procedure (cdr seq))))))


))  ; include guard
