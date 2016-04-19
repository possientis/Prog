(define (f x)
  ; code will fail if you replace 'letrec' by 'let' or 'let*'
  (letrec ((is-even?
            (lambda (n)
              (if (= n 0) #t (is-odd? (- n 1)))))
           (is-odd? (lambda (n)
              (if (= n 0) #f (is-even? (- n 1)))))
           (u (is-even? x))
           (v (is-odd? x)))
    ; returning something
    (list (or u v) (and u v))))

(display (f 3))(newline)

; question: how can we implement letrec ?

(define (g x)
  (define is-even?
    (lambda (n)
      (if (= n 0) #t (is-odd? (- n 1)))))
  (define is-odd?
    (lambda (n)
      (if (= n 0) #f (is-even? (- n 1)))))
  (define u (is-even? x))
  (define v (is-odd? x))
  (list (or u v) (and u v)))

(display (g 3))(newline)



