(define (filter pred arg)   ;returns sub-list of arg which satisfies pred
  (cond ((null? arg) '())
        (else
          (let ((item (car arg)))
            (if (pred item)
              (cons item (filter pred (cdr arg)))
              (filter pred (cdr arg)))))))

(define a '(0 -1 1 -5 7 -13 8 9 -2 -2 2 -89 76))


(define (sort comp arg)   ;returns sorted list
  (define (insert x sublist)
    (cond ((null? sublist) (list x))
          (else
            (let ((item (car sublist)))
              (if (comp x item)
                (cons x sublist)
                (cons item (insert x (cdr sublist))))))))
  (cond ((null? arg) '())
        (else (insert (car arg) (sort comp (cdr arg))))))

