(define diff-nil
  (lambda (ys) ys))

(define (diff-null? xs)
  (eq? '() (xs '())))

(define (diff-cons x xs)
  (lambda (ys) (cons x (xs ys))))

(define (diff-car xs)
  (car (xs '())))

(define (diff-cdr xs)
  (lambda (ys) 
    (cdr (xs ys))))

(define (list->diff xs)
  (if (null? xs) diff-nil
    (diff-cons (car xs) (list->diff (cdr xs)))))

(define (diff->list xs)
  (xs '()))

(define (diff-append xs ys)
  (lambda (zs) (xs (ys zs))))

(define s (list->diff '(0 1 2 3 4 5 6 7 8 9)))
(define t (list->diff '(10 11 12 13 14 15)))
(define u (diff-append s t))




