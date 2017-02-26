(load "main.scm")


(force-thunk 
  (lazy-eval 
    '(begin
       (display "abcdef\n")
       (display "+++test.scm is running+++\n"))))


(exit 0)
