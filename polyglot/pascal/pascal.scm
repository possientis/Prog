#!/usr/bin/scm
(define (pascal n)
  (if (= 1 n)
    (list 1)
    (add-list (shift-left (pascal (- n 1)))
              (shift-right(pascal (- n 1))))))

(define (shift-left seq)
  (append seq '(0)))

(define (shift-right seq)
  (cons 0 seq))

(define (add-list seq1 seq2)
  (cond ((null? seq1) '())
        ((null? seq2) '())
        (else (cons (+ (car seq1) (car seq2))
                    (add-list (cdr seq1) (cdr seq2))))))

(define (fast-pascal n)
  (if (= 1 n)
    (list 1)
    (let ((seq (fast-pascal (- n 1))))
      (add-list (shift-left seq) (shift-right seq)))))

(display (fast-pascal 20))
(newline)

(exit 0)
