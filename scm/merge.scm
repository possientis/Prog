(define (merge xs ys)
  (cond ((null? xs) ys)
        ((null? ys) xs)
        (else (if (< (car xs) (car ys))
                (cons (car xs) (merge (cdr xs) ys))
                (cons (car ys) (merge xs (cdr ys)))))))

(define (split xs)
  (cond ((null? xs) (cons '() '()))
        ((null? (cdr xs)) (cons xs '()))
        (else (let ((xr (split (cddr xs))))
                (cons (cons (car xs) (car xr))
                      (cons (cadr xs) (cdr xr)))))))

(define (merge-sort2 xs)
  (cond ((null? xs) '())
        ((null? (cdr xs)) xs)
        (else (let ((xr (split xs)))
                (merge (merge-sort (car xr))
                       (merge-sort (cdr xr)))))))

; returns a pair (ys . zs) where ys is the sorted list of the first n
; elements of xs and zs is the list of the remaining elements
(define (merge-sort-acc xs n)
  (cond ((<= n 0) (cons '() xs))
        ((= n 1) (cons (list (car xs)) (cdr xs)))
        (else (let ((n-left (quotient n 2)))
                (let ((n-right (- n n-left)))
                  (let ((ys (merge-sort-acc xs n-left)))
                    (let ((zs (merge-sort-acc (cdr ys) n-right)))
                      (cons (merge (car ys) (car zs)) (cdr zs)))))))))

; new implementation of merge-sort, better for the stack?
; uses less memory as it does not create two new lists from 'split'
(define (merge-sort xs)
  (car (merge-sort-acc xs (length xs))))

; stack friendly
(define (seq n)
  (let loop ((acc '()) (n n))
    (if (<= n 0) acc
      (loop (cons n acc) (- n 1)))))

; this will blow the stack with 100000
(define (seq2 n)
  (if (<= n 0) '()
    (cons n (seq2 (- n 1)))))


