(define object
  ;; static data member
  (let ((s_member 1))
    (lambda ()
      ;; private data
      (define d_member 2)
      ;; public interface
      (define (dispatch m)
        (cond ((eq? m 'member) d_member)
              ((eq? m 'static) s_member)
              ((eq? m 'set-member!) set-member!)
              ((eq? m 'set-static!) set-static!)
              ((eq? m 'print) (print))
              (else (display "object: unknown operation error\n"))))
      ;; private members
      (define (set-member! x)
        (set! d_member x))
      (define (set-static! x)
        (set! s_member x))
      (define (print)
        (display "static member is: ")
        (display s_member)
        (display ", while data member is: ")
        (display d_member)
        (display "\n"))
      ;; returning interface
      dispatch)))


(define a (object))
(define b (object))
(display "Object a\n")
(a 'print)
(display "Object b\n")
(b 'print)
(newline)
(newline)
(display "Setting data members to a = 3 and b = 5\n")
(newline)
((a 'set-member!) 3)
((b 'set-member!) 5)
(display "Object a\n")
(a 'print)
(display "Object b\n")
(b 'print)
(newline)
(newline)
(display "Setting static member 7 via a")
(newline)
((a 'set-static!) 7)
(display "Object a\n")
(a 'print)
(display "Object b\n")
(b 'print)
(newline)
(newline)
(display "Setting static member 9 via b")
(newline)
((b 'set-static!) 9)
(display "Object a\n")
(a 'print)
(display "Object b\n")
(b 'print)





