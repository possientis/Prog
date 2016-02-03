(load "environment.scm")

(define (environment-test)
  (define env1 (environment))
  (define env2 (environment))
  (display "environment: starting unit test\n")
  ; checking empty environment
  (if (not (env1 'empty?)) (display "environment: unit test 1.0 failing\n")) 
  (if (not (env2 'empty?)) (display "environment: unit test 1.1 failing\n")) 
  ;
  ; binding one variable to env1
  ;
  ((env1 'define!) 'a #f)
  ; should have no impact on env2
  (if (not (env2 'empty?)) (display "environment: unit test 2.0 failing\n")) 
  ; env1 should no longer be empty
  (if (env1 'empty?) (display "environment: unit test 2.1 failing\n")) 
  ; variable 'a' of env1 should be equal to #f
  (let ((val ((env1 'lookup) 'a)))
    (if (not (eq? val #f)) (display "environment: unit test 2.2 failing\n")))
  ;
  ; binding same variable to env2 
  ;
  ((env2 'define!) 'a #t)
  ; env1 and env2 should not be empty
  (if (env1 'empty?) (display "environment: unit test 3.0 failing\n")) 
  (if (env2 'empty?) (display "environment: unit test 3.1 failing\n")) 
  ; variable 'a' of env1 should be equal to #f
  (let ((val ((env1 'lookup) 'a)))
    (if (not (eq? val #f)) (display "environment: unit test 3.2 failing\n")))
  ; variable 'a' of env2 should be equal to #t
  (let ((val ((env2 'lookup) 'a)))
    (if (not (eq? val #t)) (display "environment: unit test 3.3 failing\n")))
  ;
  ; binding another variable to env1 and env2 
  ;
  ((env1 'define!) 'b "abc")
  ((env2 'define!) 'b "def")
  ; env1 and env2 should not be empty
  (if (env1 'empty?) (display "environment: unit test 4.0 failing\n")) 
  (if (env2 'empty?) (display "environment: unit test 4.1 failing\n")) 
  ; variable 'a' of env1 should be equal to #f
  (let ((val ((env1 'lookup) 'a)))
    (if (not (eq? val #f)) (display "environment: unit test 4.2 failing\n")))
  ; variable 'a' of env2 should be equal to #t
  (let ((val ((env2 'lookup) 'a)))
    (if (not (eq? val #t)) (display "environment: unit test 4.3 failing\n")))
  ; variable 'b' of env1 should be equal to "abc"
  (let ((val ((env1 'lookup) 'b)))
    (if (not (equal? val "abc")) (display "environment: unit test 4.4 failing\n")))
  ; variable 'b' of env2 should be equal to "def"
  (let ((val ((env2 'lookup) 'b)))
    (if (not (equal? val "def")) (display "environment: unit test 4.5 failing\n")))
  ;
  ; setting variables of env1 and env2 
  ;
  ((env1 'set!) 'a 12)
  ((env1 'set!) 'b '(1 2))
  ((env2 'set!) 'b #\a)
  ((env2 'set!) 'a 3.2)
  ; env1 and env2 should not be empty
  (if (env1 'empty?) (display "environment: unit test 5.0 failing\n")) 
  (if (env2 'empty?) (display "environment: unit test 5.1 failing\n")) 
  ; variable 'a' of env1 should be equal to 12
  (let ((val ((env1 'lookup) 'a)))
    (if (not (equal? val 12)) (display "environment: unit test 5.2 failing\n")))
  ; variable 'a' of env2 should be equal to 3.2
  (let ((val ((env2 'lookup) 'a)))
    (if (not (equal? val 3.2)) (display "environment: unit test 5.3 failing\n")))
  ; variable 'b' of env1 should be equal to '(1 2)
  (let ((val ((env1 'lookup) 'b)))
    (if (not (equal? val '(1 2))) (display "environment: unit test 5.4 failing\n")))
  ; variable 'b' of env2 should be equal to #\a
  (let ((val ((env2 'lookup) 'b)))
    (if (not (equal? val #\a)) (display "environment: unit test 5.5 failing\n")))
  ;
  (display "environment: unit test complete\n"))

(environment-test)
(exit 0)
