(define (this m)
  (cond ((eq? m 'name) "George")
        ((eq? m 'age) 25)
        ((eq? m 'label) 'person)
        (else (display "struct: unknown operation error\n"))))

(define that
  (list 'person
        (list 'name "george")
        (list 'age 25)))


