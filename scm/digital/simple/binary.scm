;; unsigned conversion, hence returns non-negative integer
(define (boolean-list->integer seq)
  (let loop ((seq seq) (acc 0))
    (cond ((null? seq) acc)
          ((eq? #t (car seq)) (loop (cdr seq) (+ 1 (* 2 acc))))
          ((eq? #f (car seq)) (loop (cdr seq) (* 2 acc)))
          (else "binary: boolean-list->integer: unexpected list element\n"))))

;; unsigned conversion, hence expects non-negative integer
(define (integer->boolean-list num)
  (cond ((not (integer? num))
         (display "binary: integer->boolean-list: ")
         (display "argument should be an integer\n"))
        ((< num 0)
         (display "binary: integer->boolean-list: ")
         (display "argument should be non-negative\n"))
        (else
          (let loop ((num num) (acc '()))
            (cond ((= 0 num) acc)
                  ((odd? num) (loop (quotient num 2) (cons #t acc)))
                  ((even? num) (loop (quotient num 2) (cons #f acc)))
                  (else (display "binary: integer-boolean-list: ")
                        (display "unexpected error\n")))))))

