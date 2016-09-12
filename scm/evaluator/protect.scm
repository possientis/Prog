
(define (protect proc)
  (lambda args
    (define result #f)  ; put default value here
    (call-with-current-continuation
      (lambda (cont)
        (dynamic-wind (lambda () #t)
                      (lambda ()
                        (set! result (apply proc args))
                        (set! cont #f))
                      (lambda ()
                        (if cont (cont #f))))))
    result))

(load "main.scm")

(define (thunk? object)
  (object 'thunk?))

(define new-thunk? (protect thunk?))

(define x (thunk '(+ 1 1) global-env))

(display (thunk? x))(newline)
(display (new-thunk? x))
(display (new-thunk? 3))




(newline)




