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

;; unsigned conversion, bit vector v has low order bit as v[0], etc
;; code pretty much follows logic of the 'list' version of code
;; Warning: the integer 11 is represented by the list
;; (#t #f #t #t)
;; and by the vector
;; #(#t #t #f #t)
(define (boolean-vect->integer vec)
  (let loop ((i (- (vector-length vec) 1)) (acc 0)) ; initial i -> high order bit
    (cond ((= -1 i) acc)
          ((eq? #t (vector-ref vec i)) (loop (- i 1) (+ 1 (* 2 acc))))
          ((eq? #f (vector-ref vec i)) (loop (- i 1) (* 2 acc)))
          (else "binary: boolean-vect->integer: unexpected vector element\n"))))

;; warning: size of output vector needs to be specified
(define (integer->boolean-vect num size)
  (cond ((not (integer? num))
         (display "binary: integer->boolean-vect: ")
         (display "first argument should be an integer\n"))
        ((< num 0)
         (display "binary: integer->boolean-vect: ")
         (display "first argument should be non-negative\n"))
        ((not (integer? size))
         (display "binary: integer->boolean-vect: ")
         (display "second argument should be an integer\n"))
        ((< size 0)
         (display "binary: integer->boolean-vect: ")
         (display "second argument should be non-negative\n"))
        (else (display "to be continued...\n"))))
