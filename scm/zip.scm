(define (zip seq1 seq2)
  (cond ((null? seq1) seq2)
        ((null? seq2) seq1)
        (else (cons
                (list (car seq1) (car seq2))  ; 'list' or 'cons' could do
                (zip (cdr seq1) (cdr seq2))))))
