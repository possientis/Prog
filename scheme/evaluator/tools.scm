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


(define (test-load filename message) 
  (let ((print (lambda (msg) (string-append message msg))))
    (global-env-reset!)
    (display "\ntesting strict-load ...\n")
    (assert-equals 
      (strict-load filename) unspecified-value (print ": strict-load"))

    (global-env-reset!)
    (display "\ntesting analyze-load ...\n")
    (assert-equals 
      (analyze-load filename) unspecified-value (print ": analyze-load"))

    (global-env-reset!)
    (display "\ntesting lazy-load ...\n")
    (assert-equals 
      (lazy-load filename) unspecified-value (print ": lazy-load"))

    (global-env-reset!)
    (display "\ntesting strict-eval of '(load ...) ...\n")
    (assert-equals 
      (strict-eval (list 'load filename)) 
      unspecified-value (print ": strict-eval"))

    (global-env-reset!)
    (display "\ntesting analyze-eval of '(load ...) ...\n")
    (assert-equals 
      (analyze-eval (list 'load filename)) 
      unspecified-value (print ": analyze-eval"))

    (global-env-reset!)
    (display "\ntesting lazy-eval of '(load ...) ...\n")
    (assert-equals 
      (force-thunk (lazy-eval (list 'load filename))) 
      unspecified-value (print ": lazy-eval"))

    (global-env-reset!)))

(define (test-all-files)
;  (test-load "debug.scm" "load.1") 
;  (test-load "strict-eval.scm" "load.2") 
;  (test-load "analyze-eval.scm" "load.3") 
;  (test-load "lazy-eval.scm" "load.4") 
;  (test-load "strict-apply.scm" "load.5") 
;  (test-load "analyze-apply.scm" "load.6") 
;  (test-load "lazy-apply.scm" "load.7") 
;  (test-load "strict-load.scm" "load.8") 
;  (test-load "analyze-load.scm" "load.9") 
;  (test-load "lazy-load.scm" "load.10") 
;  (test-load "strict-map.scm" "load.11") 
;  (test-load "analyze-map.scm" "load.12") 
;  (test-load "lazy-map.scm" "load.13") 
;  (test-load "new-require.scm" "load.14") 
;  (test-load "new-object-to-string.scm" "load.15") 
;  (test-load "new-display.scm" "load.16")
;  ;
;  (test-load "primitive.scm" "load.17")
;  ;
;  (test-load "primitive-procedure.scm" "load.18")
;  ;
;  (test-load "frame1.scm" "load.19")
;  (test-load "frame2.scm" "load.20")
;  (test-load "link-node.scm" "load.21")
;  (test-load "link.scm" "load.22")
;  (test-load "hash.scm" "load.23")
;  (test-load "dict.scm" "load.24")
;  (test-load "frame3.scm" "load.25")
;; (test-load "frame4.scm" "load.26")  ; (require 'hash-table)
;  (test-load "frame.scm" "load.27")
;  (test-load "environment1.scm" "load.28")
;  ;
;  (test-load "environment.scm" "load.29")
;  ;
;  (test-load "global-env.scm" "load.30")
;  ;
;  (test-load "analyze-procedure.scm" "load.31")
;  (test-load "and.scm" "load.32")
;  (test-load "application.scm" "load.33")
;  (test-load "assignment.scm" "load.34")
;  (test-load "begin.scm" "load.35")
;  (test-load "cond.scm" "load.36")
;  (test-load "defined.scm" "load.37")
;  (test-load "definition.scm" "load.38")
;  (test-load "eval-procedure.scm" "load.39")
;  (test-load "file-to-code.scm" "load.40")
;  (test-load "if.scm" "load.41")
;  (test-load "lambda.scm" "load.42")
;  (test-load "let-rec.scm" "load.43")
;  (test-load "let.scm" "load.44")
;  (test-load "let-star.scm" "load.45")
;  (test-load "named-let.scm" "load.46")
;  (test-load "not.scm" "load.47")
;  (test-load "or.scm" "load.48")
;  (test-load "quote.scm" "load.49")
;  (test-load "self-evaluating.scm" "load.50")
;  (test-load "thunk.scm" "load.51")
;  (test-load "tagged-list.scm" "load.52")
;  (test-load "unspecified.scm" "load.54")
;  (test-load "variable.scm" "load.55")
  ;
  (test-load "main.scm" "load.56")
  ;
  (test-load "frame-test.scm" "load.57")
  
  (test-load "environment-test.scm" "load.58")
  
  )

 
