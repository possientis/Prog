(define (assert-equals left right message)
  (if (not (equal? left right)) 
    (error "unit-test failure: "
           (string-append message 
                          ": value = " (object->string left)
                          ": expected = " (object->string right)))))

(define (test-expression exp value message . arg)
  (let ((env (if (null? arg) global-env (car arg))) 
        (print (lambda (msg) (string-append message msg))))
    (assert-equals 
      (strict-eval exp env) value (print ": strict-eval")) 
    (assert-equals 
      (force-thunk (lazy-eval exp env)) value (print ": lazy-eval")) 
    (assert-equals 
      (analyze-eval exp env) value (print ": analyze"))))

; same semantics as test-expression, except that expression is forced
; following evaluation and prior to comparing to expected value
(define (test-forced-expression exp value message . arg)
  (let ((env (if (null? arg) global-env (car arg))) 
        (print (lambda (msg) (string-append message msg))))
    (assert-equals 
      (force-thunk (strict-eval exp env)) value (print ": strict-eval")) 
    (assert-equals 
      (force-thunk (lazy-eval exp env)) value (print ": lazy-eval")) 
    (assert-equals 
      (force-thunk (analyze-eval exp env)) value (print ": analyze"))))


(define (test-load filename message) 
  (let ((print (lambda (msg) (string-append message msg))))
    (global-env-reset!)
    (assert-equals 
      (strict-load filename) unspecified-value (print ": strict-load"))

    (global-env-reset!)
    (assert-equals 
      (analyze-load filename) unspecified-value (print ": analyze-load"))

    (global-env-reset!)
    (assert-equals 
      (lazy-load filename) unspecified-value (print ": lazy-load"))

    (global-env-reset!)
    (assert-equals 
      (strict-eval (list 'load filename)) 
      unspecified-value (print ": strict-eval"))

    (global-env-reset!)
    (assert-equals 
      (analyze-eval (list 'load filename)) 
      unspecified-value (print ": analyze-eval"))

    (global-env-reset!)
    (assert-equals 
      (force-thunk (lazy-eval (list 'load filename))) 
      unspecified-value (print ": lazy-eval"))

    (global-env-reset!)))


