
(define (driver-loop)
  (display "type in some input:")
  (let ((input (read)))
    (display "input = ")(display input)
    (cond ((number? input) (display " (number)\n"))
          ((string? input) (display " (string)\n"))
          ((char? input) (display " (char)\n"))
          ((boolean? input)(display " (boolean)\n"))
          ((symbol? input) (display " (symbol)\n"))
          ((list? input) (display " (list)\n"))
          ((vector? input) (display " (vector)\n"))
          (else (display " (unknown type)\n"))))
  (driver-loop))

(driver-loop)

(exit 0)
