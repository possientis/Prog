(load "eval.scm")
(load "environment-test.scm")
(load "primitive-test.scm")
(load "global-env-test.scm")

(define (eval-test)
  ;
  ;
  ;
  (display "eval: starting unit test\n")
  ;
  ;
  (display "eval: unit test complete\n"))

(environment-test)
(primitive-test)
(global-env-test)
(eval-test)
(exit 0)
