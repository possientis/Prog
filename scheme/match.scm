(define (match pred l)  ; returns #f or first element in list matching pred
  (cond ((null? l) #f)  ; no match on empty list
        (else (let ((item (car l))) ; item is first on the list
                (cond ((pred item) item)
                      (else (match pred (cdr l))))))))

