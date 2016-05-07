(load "eval.scm")
(define input-prompt ";;; M-Eval input:")
(define output-prompt ";;; M-Eval value:")

(define (driver-loop)
  (prompt-for-input input-prompt)
  (newline)(display ">")
  (let ((input (read)))
    (let ((output1 (eval input global-env)))
      (announce-output output-prompt)
      (user-print output1)))
  (driver-loop))

(define (prompt-for-input str)
  (newline)(display str))

(define (announce-output str)
  (display str)(newline))

(define (user-print object)
  (if (compound-procedure? object)
    (display (list 'compound-procedure
                   (procedure-parameters object)
                   (procedure-body object)
                   '<procedure-env>))
    (display object))(newline))


(driver-loop)
