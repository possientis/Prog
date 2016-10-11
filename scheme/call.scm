(define (serialize p)
  (define (q . args)
    (print "This procedure has been serialized")
    (apply p args))
  q)


(define (serial p)
  (define q
    (lambda (l)
      (print "This procedure has been serialized even more")
      (apply p l)))
  q)
