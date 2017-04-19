(use-modules (srfi srfi-9))
(use-modules (srfi srfi-9 gnu))

(define-record-type employee
  (make-employee name age salary)
  employee?
  (name employee-name)
  (age employee-age set-employee-age!)
  (salary employee-salary set-employee-salary!))

(define a (make-employee "john" 34 12000))

(display "(employee? a) = ")(display (employee? a))(newline)
(display "(employee? \"abc\") = ")(display (employee? "abc"))(newline)
(display "(employee-name a) = ")(display (employee-name a))(newline)
(display "(employee-age a) = ")(display (employee-age a))(newline)
(display "(employee-salary a) = ")(display (employee-salary a))(newline)

(display "a = ")(display a)(newline)

(set-record-type-printer! employee
  (lambda (record port)
    (write-char #\[ port)
    (display (employee-name record) port)
    (write-char #\] port)))

(display "a = ")(display a)(newline)


