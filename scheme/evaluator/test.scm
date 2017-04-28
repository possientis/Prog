; loading interpreter
(load "main.scm") 

(strict-eval '(load "main.scm"))
(strict-eval '(set-debug #t))

(define (do-run expr)
  (force-thunk (lazy-eval expr)))


(define code1
  (quote
    (quote

      ( ; run the procedure defined as ...

       (lambda () 
         (define x 0)
         (display x)      ; issue1: not executed !! , issue2: would fail anyway 
         (newline)        ; code will fail if this line commented out
       )

      ) ; end of run procedure

      )))

(define code2
  (quote
    (quote

     (begin 
       (display "This is not the last\n")
       (display "only the last line will be executed\n")
     )

      )))

(do-run (list 'strict-eval code1))(newline)
;(do-run '(strict-eval '(begin (display "A\n")(display "B\n"))))

(exit 0)


