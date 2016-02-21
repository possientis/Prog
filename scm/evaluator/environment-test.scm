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
  ; extending environment with empty frame
  ;
  (let ((env3 ((env1 'extended) '() '())) (env4 ((env2 'extended) '() '())))
    ; env3 and env4 should not be empty
    (if (env3 'empty?) (display "environment: unit test 6.0 failing\n")) 
    (if (env4 'empty?) (display "environment: unit test 6.1 failing\n")) 
    ; variable 'a' of env3 should be equal to 12
    (let ((val ((env3 'lookup) 'a)))
      (if (not (equal? val 12)) (display "environment: unit test 6.2 failing\n")))
    ; variable 'a' of env4 should be equal to 3.2
    (let ((val ((env4 'lookup) 'a)))
      (if (not (equal? val 3.2)) (display "environment: unit test 6.3 failing\n")))
    ; variable 'b' of env3 should be equal to '(1 2)
    (let ((val ((env3 'lookup) 'b)))
      (if(not(equal? val '(1 2))) (display "environment: unit test 6.4 failing\n")))
    ; variable 'b' of env4 should be equal to #\a
    (let ((val ((env4 'lookup) 'b)))
      (if (not (equal? val #\a)) (display "environment: unit test 6.5 failing\n"))))
  ; this should have no impact on env1 and env2
  ; env1 and env2 should not be empty
  (if (env1 'empty?) (display "environment: unit test 7.0 failing\n")) 
  (if (env2 'empty?) (display "environment: unit test 7.1 failing\n")) 
  ; variable 'a' of env1 should be equal to 12
  (let ((val ((env1 'lookup) 'a)))
    (if (not (equal? val 12)) (display "environment: unit test 7.2 failing\n")))
  ; variable 'a' of env2 should be equal to 3.2
  (let ((val ((env2 'lookup) 'a)))
    (if (not (equal? val 3.2)) (display "environment: unit test 7.3 failing\n")))
  ; variable 'b' of env1 should be equal to '(1 2)
  (let ((val ((env1 'lookup) 'b)))
    (if (not (equal? val '(1 2))) (display "environment: unit test 7.4 failing\n")))
  ; variable 'b' of env2 should be equal to #\a
  (let ((val ((env2 'lookup) 'b)))
    (if (not (equal? val #\a)) (display "environment: unit test 7.5 failing\n")))
  ;
  ; extending environment with single additional name
  ;
  (let ((env3 ((env1 'extended) '(c) '(3))) (env4 ((env2 'extended) '(c) '(4))))
    ; env3 and env4 should not be empty
    (if (env3 'empty?) (display "environment: unit test 8.0 failing\n")) 
    (if (env4 'empty?) (display "environment: unit test 8.1 failing\n")) 
    ; variable 'a' of env3 should be equal to 12
    (let ((val ((env3 'lookup) 'a)))
      (if (not (equal? val 12)) (display "environment: unit test 8.2 failing\n")))
    ; variable 'a' of env4 should be equal to 3.2
    (let ((val ((env4 'lookup) 'a)))
      (if (not (equal? val 3.2)) (display "environment: unit test 8.3 failing\n")))
    ; variable 'b' of env3 should be equal to '(1 2)
    (let ((val ((env3 'lookup) 'b)))
      (if(not(equal? val '(1 2))) (display "environment: unit test 8.4 failing\n")))
    ; variable 'b' of env4 should be equal to #\a
    (let ((val ((env4 'lookup) 'b)))
      (if (not (equal? val #\a)) (display "environment: unit test 8.5 failing\n")))
    ; variable 'c' of env3 should be equal to 3
    (let ((val ((env3 'lookup) 'c)))
      (if(not(equal? val 3)) (display "environment: unit test 8.6 failing\n")))
    ; variable 'c' of env4 should be equal to 4
    (let ((val ((env4 'lookup) 'c)))
      (if (not (equal? val 4)) (display "environment: unit test 8.7 failing\n"))))
  ; this should have no impact on env1 and env2
  ; env1 and env2 should not be empty
  (if (env1 'empty?) (display "environment: unit test 9.0 failing\n")) 
  (if (env2 'empty?) (display "environment: unit test 9.1 failing\n")) 
  ; variable 'a' of env1 should be equal to 12
  (let ((val ((env1 'lookup) 'a)))
    (if (not (equal? val 12)) (display "environment: unit test 9.2 failing\n")))
  ; variable 'a' of env2 should be equal to 3.2
  (let ((val ((env2 'lookup) 'a)))
    (if (not (equal? val 3.2)) (display "environment: unit test 9.3 failing\n")))
  ; variable 'b' of env1 should be equal to '(1 2)
  (let ((val ((env1 'lookup) 'b)))
    (if (not (equal? val '(1 2))) (display "environment: unit test 9.4 failing\n")))
  ; variable 'b' of env2 should be equal to #\a
  (let ((val ((env2 'lookup) 'b)))
    (if (not (equal? val #\a)) (display "environment: unit test 9.5 failing\n")))
  ;
  ; extending environment with single additional name which already exists
  ;
  (let ((env3 ((env1 'extended) '(a) '(11))) (env4 ((env2 'extended) '(b) '(22))))
    ; env3 and env4 should not be empty
    (if (env3 'empty?) (display "environment: unit test 10.0 failing\n")) 
    (if (env4 'empty?) (display "environment: unit test 10.1 failing\n")) 
    ; variable 'a' of env3 should *** now *** be equal to 11
    (let ((val ((env3 'lookup) 'a)))
      (if (not (equal? val 11)) (display "environment: unit test 10.2 failing\n")))
    ; variable 'a' of env4 should be equal to 3.2
    (let ((val ((env4 'lookup) 'a)))
      (if (not (equal? val 3.2)) (display "environment: unit test 10.3 failing\n")))
    ; variable 'b' of env3 should be equal to '(1 2)
    (let ((val ((env3 'lookup) 'b)))
      (if(not(equal? val '(1 2)))(display "environment: unit test 10.4 failing\n")))
    ; variable 'b' of env4 should *** now *** be equal to 22
    (let ((val ((env4 'lookup) 'b)))
      (if (not (equal? val 22)) (display "environment: unit test 10.5 failing\n"))))
  ; this should have no impact on env1 and env2
  ; env1 and env2 should not be empty
  (if (env1 'empty?) (display "environment: unit test 11.0 failing\n")) 
  (if (env2 'empty?) (display "environment: unit test 11.1 failing\n")) 
  ; variable 'a' of env1 should be equal to 12
  (let ((val ((env1 'lookup) 'a)))
    (if (not (equal? val 12)) (display "environment: unit test 11.2 failing\n")))
  ; variable 'a' of env2 should be equal to 3.2
  (let ((val ((env2 'lookup) 'a)))
    (if (not (equal? val 3.2)) (display "environment: unit test 11.3 failing\n")))
  ; variable 'b' of env1 should be equal to '(1 2)
  (let ((val ((env1 'lookup) 'b)))
    (if (not(equal? val '(1 2))) (display "environment: unit test 11.4 failing\n")))
  ; variable 'b' of env2 should be equal to #\a
  (let ((val ((env2 'lookup) 'b)))
    (if (not (equal? val #\a)) (display "environment: unit test 11.5 failing\n")))
  ;
  ; extending environment with two additional names
  ;
  (let ((env3 ((env1 'extended) '(c d) '(3 #\a))) 
        (env4 ((env2 'extended) '(c d) '(4 #\b))))
    ; env3 and env4 should not be empty
    (if (env3 'empty?) (display "environment: unit test 12.0 failing\n")) 
    (if (env4 'empty?) (display "environment: unit test 12.1 failing\n")) 
    ; variable 'a' of env3 should be equal to 12
    (let ((val ((env3 'lookup) 'a)))
      (if (not (equal? val 12)) (display "environment: unit test 12.2 failing\n")))
    ; variable 'a' of env4 should be equal to 3.2
    (let ((val ((env4 'lookup) 'a)))
      (if (not (equal? val 3.2)) (display "environment: unit test 12.3 failing\n")))
    ; variable 'b' of env3 should be equal to '(1 2)
    (let ((val ((env3 'lookup) 'b)))
      (if(not(equal? val '(1 2)))(display "environment: unit test 12.4 failing\n")))
    ; variable 'b' of env4 should be equal to #\a
    (let ((val ((env4 'lookup) 'b)))
      (if (not (equal? val #\a)) (display "environment: unit test 12.5 failing\n")))
    ; variable 'c' of env3 should be equal to 3
    (let ((val ((env3 'lookup) 'c)))
      (if(not(equal? val 3)) (display "environment: unit test 12.6 failing\n")))
    ; variable 'c' of env4 should be equal to 4
    (let ((val ((env4 'lookup) 'c)))
      (if (not (equal? val 4)) (display "environment: unit test 12.7 failing\n")))
    ; variable 'd' of env3 should be equal to #\a
    (let ((val ((env3 'lookup) 'd)))
      (if(not(equal? val #\a)) (display "environment: unit test 12.8 failing\n")))
    ; variable 'd' of env4 should be equal to 4
    (let ((val ((env4 'lookup) 'd)))
      (if (not(equal? val #\b)) (display "environment: unit test 12.9 failing\n"))))
  ; this should have no impact on env1 and env2
  ; env1 and env2 should not be empty
  (if (env1 'empty?) (display "environment: unit test 13.0 failing\n")) 
  (if (env2 'empty?) (display "environment: unit test 13.1 failing\n")) 
  ; variable 'a' of env1 should be equal to 12
  (let ((val ((env1 'lookup) 'a)))
    (if (not (equal? val 12)) (display "environment: unit test 13.2 failing\n")))
  ; variable 'a' of env2 should be equal to 3.2
  (let ((val ((env2 'lookup) 'a)))
    (if (not (equal? val 3.2)) (display "environment: unit test 13.3 failing\n")))
  ; variable 'b' of env1 should be equal to '(1 2)
  (let ((val ((env1 'lookup) 'b)))
    (if (not(equal? val '(1 2))) (display "environment: unit test 13.4 failing\n")))
  ; variable 'b' of env2 should be equal to #\a
  (let ((val ((env2 'lookup) 'b)))
    (if (not (equal? val #\a)) (display "environment: unit test 13.5 failing\n")))
  ;
  ; deleting names from environments
  ;
  ((env1 'delete!) 'a)
  ((env2 'delete!) 'b)
  (if (env1 'empty?) (display "environment: unit test 14.0 failing\n")) 
  (if (env2 'empty?) (display "environment: unit test 14.1 failing\n")) 
  ; variable 'b' of env1 should be equal to '(1 2)
  (let ((val ((env1 'lookup) 'b)))
    (if (not(equal? val '(1 2))) (display "environment: unit test 14.2 failing\n")))
  ; variable 'a' of env2 should be equal to 3.2
  (let ((val ((env2 'lookup) 'a)))
    (if (not (equal? val 3.2)) (display "environment: unit test 14.3 failing\n")))
  ;
  ; deleting last names from environments
  ;
  ((env1 'delete!) 'b)
  ((env2 'delete!) 'a)

  ; both environment should now be empty
  (if (not (env1 'empty?)) (display "environment: unit test 15.0 failing\n")) 
  (if (not (env2 'empty?)) (display "environment: unit test 15.1 failing\n")) 

  (display "environment: unit test complete\n"))

(environment-test)
(exit 0)
