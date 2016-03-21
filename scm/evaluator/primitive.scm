(load "load-file.scm")
(define (primitive-implementation proc) (cadr proc))

(define primitive-procedures
  (list (list 'car car)
        (list 'cdr cdr)
        (list 'cons cons)
        (list 'null? null?)
        (list '+ +)
        (list '* *)
        (list '- -)
        (list '/ /)
        (list 'modulo modulo)
        (list 'equal? equal?)
        (list 'eq?    eq?)
        (list 'display display)
        (list 'newline newline)
        (list 'load    load-file)
        ; more to be included
        ))
(define (primitive-procedure-names) (map car primitive-procedures))
(define (primitive-procedure-objects)
  (map (lambda (proc) (list 'primitive (cadr proc))) primitive-procedures))

