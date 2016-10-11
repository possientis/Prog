(load "main.scm")


(define input-prompt ";;; Lazy-Eval input:")
(define output-prompt ";;; Lazy-Eval value:")

(define (driver-loop)
  (prompt-for-input input-prompt)
  (newline)(display ">")
  (let ((input (read)))
    (let ((output (lazy-eval input global-env)))
      (announce-output output-prompt)
      (user-print (force-thunk output))))
  (driver-loop))

(define (prompt-for-input str)
  (newline)(display str))

(define (announce-output str)
  (display str)(newline))

(define (user-print object)
  (display "eval:         ") (display object)(newline))

(driver-loop)

