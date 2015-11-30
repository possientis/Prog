(define (append xs ys)
  (if (null? xs) ys
    (cons (car xs) (append (cdr xs) ys))))

(define (list-ref xs n)
  (if (= n 1) (car xs)
    (list-ref (cdr xs) (- n 1))))

(define (list-sum xs)
  (if (null? xs) 0
    (+ (car xs) (list-sum (cdr xs)))))

(define (length xs)
  (if (null? xs) 0
    (+ 1 (length (cdr xs)))))

(define (reverse xs)
  (let iter ((xs xs) (ys '()))
    (if (null? xs) ys
      (iter (cdr xs) (cons (car xs) ys)))))

