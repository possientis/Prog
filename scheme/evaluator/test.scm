; loading interpreter
(load "main.scm") 

(strict-eval '(load "main.scm"))
(strict-eval '(set-debug #t))

(define (do-run expr)
  (force-thunk (lazy-eval expr)))


(define code
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

(do-run (list 'strict-eval code 'global-env))(newline)

(exit 0)


