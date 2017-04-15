; loading interpreter
(load "main.scm") 
(set-debug #f)

;(define mode 'lazy)
;(define (do-run expr)
;  (if (eq? mode 'strict)
;    (strict-eval expr)
;    (if (eq? mode 'lazy)
;      (force-thunk (lazy-eval expr))
;      (error "do-run: evaluation mode not supported"))))
      

; loading interpreter into global-env
(force-thunk (lazy-eval '(load "main.scm")))


;(newline)
;(display "primitives are: ")
;(display (strict-eval '(primitive-procedure-names)))(newline) 


; and global-env should also have a global-env
(newline)
(newline)
(display "global-env = ")(display (strict-eval '(global-env 'to-string)))(newline)


;do-run '(define base-env (environment)))
;(do-run '(define names (primitive-procedure-names)))
;(do-run '(define objects (primitive-procedure-objects)))
;(do-run '(define env ((base-env 'extended) names objects)))



(newline)
(newline)
;(display "base-env = ")(display (strict-eval '(base-env 'to-string)))(newline)
(newline)
;(display "env = ")(display (strict-eval '(env 'to-string)))(newline)




; this fails
;(display (strict-eval '((global-env 'lookup) '+)))(newline)

; yet this fails
;(strict-eval '(strict-eval '+))


(exit 0)



;string->symbol, vector-fill!, symbol?, vector-ref, string?, string-append, vector-length, vector-set!

