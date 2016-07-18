(load "main.scm")


(define input-prompt ";;; M-Eval input:")
(define output-prompt ";;; M-Eval value:")

(define (driver-loop)
  (prompt-for-input input-prompt)
  (newline)(display ">")
  (let ((input (read)))
    (let ((output ((analyze input) global-env)))
      (announce-output output-prompt)
      (user-print output)))
  (driver-loop))

(define (prompt-for-input str)
  (newline)(display str))

(define (announce-output str)
  (display str)(newline))

(define (user-print object)
  (display "eval:         ") (display object)(newline))

(driver-loop)


