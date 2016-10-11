(define (digit? x)
  (cond ((eq? x #\0) #t)
        ((eq? x #\1) #t)
        ((eq? x #\2) #t)
        ((eq? x #\3) #t)
        ((eq? x #\4) #t)
        ((eq? x #\5) #t)
        ((eq? x #\6) #t)
        ((eq? x #\7) #t)
        ((eq? x #\8) #t)
        ((eq? x #\9) #t)
        (else #f)))

(define (parse-digit seq)
  (cond ((null? seq) (list '())) 
        ((digit? (car seq)) (cons (list (car seq)) (cdr seq)))
        (else (cons '() seq))))

(define (parse-int seq)
  (let loop ((acc '())(left seq))
    (let ((res (parse-digit left)))
      (if (eq? '() (car res))  ; attempt to find digit failed
        (cons acc left)
        ; else
        (let ((digit (caar res))(new (cdr res)))
          (loop (cons digit acc) new))))))

(define seq1 (string->list "123a"))
(define seq2 (string->list "qw23"))
(define seq3 (string->list ""))

(display (parse-digit seq1))(newline)
(display (parse-digit seq2))(newline)
(display (parse-digit seq3))(newline)
(display (parse-int seq1))(newline)
(display (parse-int seq2))(newline)
(display (parse-int seq3))(newline)
        
