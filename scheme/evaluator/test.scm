; loading interpreter
(load "main.scm") 

(force-thunk (lazy-eval '(load "main.scm")))
(force-thunk (lazy-eval '(load "tools.scm")))

(define code 
  '(test-expression 
     (quote (let loop ((i 5) (acc 1)) 
        (if (equal? 1 i) 
          acc 
          (loop (- i 1) (* i acc))))) 
         120 "named-let.1")
)

(display (force-thunk (lazy-eval code)))


(exit 0)


