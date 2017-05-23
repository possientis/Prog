; scm only

; remove the comma ',' operator below to understand its significance
; remove the '@' below and see what happens



(defmacro (let1 ((name value)) . body)
  `((lambda (,name) ,@body) ,value))

(display (macroexpand '(let1 ((x 5)) (* x x))))(newline)
(display (let1 ((x 5)) (* x x)))(newline)

(exit 0)



