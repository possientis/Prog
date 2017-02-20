;(load "unit-test.scm")

(load "main.scm") ; defining 'strict-eval'
;(strict-eval '(load "unit-test.scm"))


(strict-eval '(load "main.scm"))  ; defning 'strict-eval'

(strict-eval '(strict-eval '(load "unit-test.scm")))


(exit 0)
