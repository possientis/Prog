(load "environment.scm")

(define (environment-test)
  (define env1 (environment))
  (define env2 (environment))
  (display "environment: starting unit test\n")
  ; checking empty environment
  (if (not (env1 'empty?)) (display "environment: unit test 1.0 failing\n")) 
  (if (not (env2 'empty?)) (display "environment: unit test 1.1 failing\n")) 
  ; binding one variable
  ((env1 'define!) 'a #f)
  ; should have no impact on env2
  (if (not (env2 'empty?)) (display "environment: unit test 2.0 failing\n")) 
  ; env1 should no longer be empty
  (if (env1 'empty?) (display "environment: unit test 2.1 failing\n")) 
  ; variable 'a should be equal to #f
  (let ((val ((env1 'lookup) 'a)))
    (if (not (eq? val #f)) (display "environment: unit test 2.2 failing\n")))


  (display "environment: unit test complete\n"))

(environment-test)
(exit 0)
