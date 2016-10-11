(load "prime.scm")

(define (accumulate op init seq)
  (if (null? seq)
    init
    (op (car seq) (accumulate op init (cdr seq)))))

(define (new-map p seq)
  (accumulate
    (lambda (x y) (cons (p x) y))
    '()
    seq))

(define (square x) (* x x))

(define (new-append seq1 seq2)
  (accumulate cons seq2 seq1))

(define (new-length seq)
  (accumulate
    (lambda (x y) (+ 1 y))
    0
    seq))

(define (horner-eval x coeffs)
  ;; coeffs should be a list
  ;; 1 + 2x + 4x^2 -> (1 2 4)
  (accumulate
    (lambda (u v) (+ u (* x v)))
    0
    coeffs))

(define (enumerate-tree tree)
  (cond ((null? tree) '())
        ((not (pair? tree)) (list tree))
        (else (append (enumerate-tree (car tree)) (enumerate-tree (cdr tree))))))


(define (accumulate-n op init seqs)
  (if (null? (car seqs))
    '()
    (cons (accumulate op init (map car seqs))
          (accumulate-n op init (map cdr seqs)))))

(define (enumerate-interval n m)
  (if (< m n)
    '()
    (cons n (enumerate-interval (+ 1 n) m))))

(define (generate2 n)
  (accumulate append '()
    (map (lambda (i)
          (map (lambda (j)
                  (list i j))
                (enumerate-interval 1 (- i 1))))
        (enumerate-interval 1 n))))

(define (flatmap proc seq)
  (accumulate append '() (map proc seq)))

(define  (generate-pairs n)
  (flatmap
    (lambda (i)
      (map (lambda (j)
             (list i j))
           (enumerate-interval 1 (- i 1))))
    (enumerate-interval 1 n)))

(define (prime-sum? pair)
  (prime? (+ (car pair) (cadr pair))))

(define (filter-list proc l)
  (cond ((null? l) '())
        ((proc (car l)) (cons (car l) (filter-list proc (cdr l))))
        (else (filter-list proc (cdr l)))))

(define (make-pair-sum pair)
  (list (car pair) (cadr pair) (+ (car pair) (cadr pair))))

(define (prime-sum-pairs n)
  (map make-pair-sum
       (filter-list
         prime-sum?
         (generate-pairs n))))


