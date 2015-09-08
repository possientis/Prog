(define myList (list
                 (cons 0 'a)
                 (cons 1 'b)
                 (cons 2 'c)))

(define (search key table)
  (assoc key table))
