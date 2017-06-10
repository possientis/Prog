(define a (async (lambda () (display "thunk a is running...\n"))))
(define b (async (lambda () (display "thunk b is running...\n"))))

(display "marking the user asyncs for future execution\n")

(async-mark a)
;(async-mark b)

(display "running user asyncs which are marked a\n") 
(run-asyncs (list a b))


(exit 0)



