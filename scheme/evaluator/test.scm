; loading interpreter
(load "main.scm") 

(force-thunk (lazy-eval '(load "main.scm")))
(force-thunk (lazy-eval '(set-debug #t)))

(define (wrap code)
  (list 'strict-eval code))

(define code1                 ; fails under lazy-eval
  (quote
    (quote 
      (let loop ((i 5) (acc 1)) 
        (if (equal? 1 i) 
          acc 
          (loop (- i 1) (* i acc)))))))


(define code2                 ; succeeds under lazy-eval
  (quote 
    (let loop ((i 5) (acc 1)) 
      (if (equal? 1 i) 
        acc 
        (loop (- i 1) (* i acc))))))

(newline)
(display "code1 (fails):\n")(display (wrap code1))(newline)
(newline)
(display "code2 (succeeds):\n")(display (wrap code2))(newline)

(newline)
(display (force-thunk (lazy-eval (wrap code2))))(newline)

(newline)
(display "value1 = ")(display (eval code1))(newline)
(display "value2 = ")(display (eval code2))(newline)

(display 
  (force-thunk 
    (lazy-eval
      (quote
        (let loop ((i 5) (acc 1)) 
          (if (equal? 1 i) 
            acc 
            (loop (- i 1) (* i acc))))))))


(exit 0)


