; loading interpreter
(load "main.scm") 

(force-thunk (lazy-eval '(load "main.scm")))
(force-thunk (lazy-eval '(set-debug #t)))

(define (do-run expr)
  (force-thunk (lazy-eval expr)))


(define code
  (quote
    (quote
      ((lambda (i acc) 
         (define loop 
           (lambda (i acc) (if (equal? 1 i) acc (loop (- i 1) (* i acc))))) 
         (loop i acc)) 5 1))))


(display (do-run (list 'strict-eval code 'global-env)))(newline)

(exit 0)


