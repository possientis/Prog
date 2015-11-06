(define (stat m)
  (string-append "static: " m))

(define (dyn m)
  (string-append "dynamic: " m))

(let ((P #f)(Q #f))
  (set! Q (lambda (x) (display (stat x))(newline)))
  (set! P (lambda (x) (Q x)))
  (let ((Q #f))
    (set! Q (lambda (x) (display (dyn x))(newline)))
    (P "Hello world!")))
