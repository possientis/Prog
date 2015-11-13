(define (seq n)
  (let loop ((l '()) (i n))
    (if (< i 1)
      l
      (loop (cons i l) (- i 1)))))

; 'seq2' just there for no reason
; memory leak as reference to seq always kept
(define (sum x seq1 seq2)
  (if (null? seq1) 
    x
    (sum (+ x (car seq1)) (cdr seq1) seq2)))

(define x (seq 10000))

(display (sum 0 x x))(newline)


