(define (append xs ys)
  (if (null? xs) ys
    (cons (car xs) (append (cdr xs) ys))))

(define (list-ref xs n)
  (if (= n 1) (car xs)
    (list-ref (cdr xs) (- n 1))))

(define (list-sum xs)
  (if (null? xs) 0
    (+ (car xs) (list-sum (cdr xs)))))

(define (slow-reverse xs)
  (if (null? xs) '()
    (append (reverse (cdr xs)) (list (car xs)))))

(define (length-iter i xs)
  (if (null? xs) i
    (length-iter (+ i 1) (cdr xs))))


(define (length xs)
  (if (null? xs) 0
    (+ 1 (length (cdr xs)))))

(define (fast-reverse xs)
  (let iter ((xs xs) (ys '()))
    (if (null? xs) ys
      (iter (cdr xs) (cons (car xs) ys)))))

(define (reverse2 xs)
  (define (iter xs ys)
    (if (null? xs) ys
      (iter (cdr xs) (cons (car xs) ys))))
  (iter xs '()))

(define (reverse xs)
  (letrec ((iter
          (lambda (xs ys)
            (if (null? xs) ys
              (iter (cdr xs) (cons (car xs) ys))))))
    (iter xs '())))













