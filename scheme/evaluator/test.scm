; loading interpreter
(load "main.scm") 

; loading interpreter into global-env
(force-thunk (lazy-eval '(load "main.scm")))


(newline)
(display "primitives are: ")
(display (strict-eval '(primitive-procedure-names)))(newline) 


; and global-env should also have a global-env
(newline)
(newline)
(display "global-env = ")(display (strict-eval '(global-env 'to-string)))(newline)


(force-thunk (lazy-eval '(define base-env (environment))))
(force-thunk (lazy-eval '(define names (primitive-procedure-names))))
(force-thunk (lazy-eval '(define objects (primitive-procedure-objects))))
(force-thunk (lazy-eval '(define name (cons (car names) (cadr names)))))
(force-thunk (lazy-eval '(define object (cons (car objects) (cadr objects)))))
(force-thunk (lazy-eval '(define env ((base-env 'extended) 
                                      name object))))




(newline)
(newline)
(display "base-env = ")(display (strict-eval '(base-env 'to-string)))(newline)
(newline)
(display "name  = ")(display (strict-eval 'name))(newline)
(newline)
(display "object  = ")(display (strict-eval 'object))(newline)
(newline)
(display "env = ")(display (strict-eval '(env 'to-string)))(newline)




; this fails
;(display (strict-eval '((global-env 'lookup) '+)))(newline)

; yet this fails
;(strict-eval '(strict-eval '+))


(exit 0)



;string->symbol, vector-fill!, symbol?, vector-ref, string?, string-append, vector-length, vector-set!

