(let ((name-encapsulate #f))
  (define some-variable 23)
  (display some-variable)(newline))

; (display some-variable)(newline) ; --> unbound error

(let ((name-encapsulate #f))
  (load "load-test")  ; (define some-variable 45)
  (display some-variable)(newline))

(display some-variable)(newline) ; no error this time

; conclusion: load seems run, not from the local environment, but from the
; global environment
