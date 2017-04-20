; loading interpreter
(load "main.scm") 

(force-thunk (lazy-eval '(load "main.scm")))
(force-thunk (lazy-eval '(load "tools.scm")))
(force-thunk (lazy-eval '(set-debug #t)))

(define code 
  '(test-expression 
     (quote (let loop ((i 5) (acc 1)) 
        (if (equal? 1 i) 
          acc 
          (loop (- i 1) (* i acc))))) 
         120 "named-let.1")
)

(define code2
  '(let loop ((i 5) (acc 1)) 
     (if (equal? 1 i) 
       acc 
       (loop (- i 1) (* i acc))))) 

(define code3 
  (list 'assert-equals (list 'strict-eval code2) 120 "abc"))

;(force-thunk (lazy-eval code3))  ; this does not fail ... but why?
 
(force-thunk (lazy-eval code))


(exit 0)


