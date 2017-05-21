(define (debug n)
  (if (eq? n 0) 
    (display "[DEBUG]: cond: else\n")
    (if (eq? n 1)
      (display "[DEBUG]: cond: base\n")
      (if (eq? n 2)
        (display "[DEBUG]: cond: main:\n")
        (display "[DEBUG]: debug: wrong argument\n")))))

(define-syntax cond
  (lambda (x)
    (syntax-case x (else debug)
      ((_ (else e1 e2 ...)) (syntax (begin (debug 0) e1 e2 ...)))
      ((_ (e0 e1 e2 ...)) (syntax (if e0 (begin (debug 1) e1 e2 ...))))
      ((_ (e0 e1 e2 ...) c1 c2 ...)
       (syntax (if e0 (begin (debug 2) e1 e2 ...) (cond c1 c2 ...)))))))

(cond (else (display "cond.0.0\n")))
(cond (else (display "cond.1.0 ") (display "cond.1.1\n")))
(cond (else (display "cond.2.0 ") (display "cond.2.1 ") (display "cond.2.2\n")))

(cond (#t (display "cond.3.0\n")))
(cond (#t (display "cond.4.0 ") (display "cond.4.1\n")))
(cond (#t (display "cond.5.0 ") (display "cond.5.1 ") (display "cond.5.2\n")))

(cond (#t   (display "cond.6.0\n"))
      (else (display "cond.6.1\n")))
(cond (#t   (display "cond.7.0 ") (display "cond.7.1\n"))
      (else (display "cond.7.2\n")))
(cond (#t   (display "cond.8.0 ") (display "cond.8.1 ") (display "cond.8.2\n"))
      (else (display "cond.8.3\n")))

(cond (#f   (display "cond.9.1\n"))
      (else (display "cond.9.0\n")))
(cond (#f   (display "cond.10.2 "))
      (else (display "cond.10.0 ") (display "cond.10.1\n")))
(cond (#f   (display "cond.11.3 "))
      (else (display "cond.11.0 ") (display "cond.11.1 ") (display "cond.11.2\n")))


(define-syntax cond2
  (lambda (x)
    (syntax-case x ()
      ((_ (e0 e1 e2 ...))
       (and (identifier? (syntax e0))
            (free-identifier=? (syntax e0) (syntax else)))
       (syntax (begin e1 e2 ...)))
      ((_ (e0 e1 e2 ...)) (syntax (if e0 (begin e1 e2 ...))))
      ((_ (e0 e1 e2 ...) c1 c2 ...)
       (syntax (if e0 (begin e1 e2 ...) (cond c1 c2 ...)))))))


(newline)(newline)
(cond2 (else (display "cond2.0.0\n")))
(cond2 (else (display "cond2.1.0 ") (display "cond2.1.1\n")))
(cond2 (else (display "cond2.2.0 ") (display "cond2.2.1 ") (display "cond2.2.2\n")))

(cond2 (#t (display "cond2.3.0\n")))
(cond2 (#t (display "cond2.4.0 ") (display "cond2.4.1\n")))
(cond2 (#t (display "cond2.5.0 ") (display "cond2.5.1 ") (display "cond2.5.2\n")))

(cond2  (#t   (display "cond2.6.0\n"))
        (else (display "cond2.6.1\n")))
(cond2  (#t   (display "cond2.7.0 ") (display "cond2.7.1\n"))
        (else (display "cond2.7.2\n")))
(cond2  (#t   (display "cond2.8.0 ") (display "cond2.8.1 ") (display "cond2.8.2\n"))
        (else (display "cond2.8.3\n")))

(cond2  (#f   (display "cond2.9.1\n"))
        (else (display "cond2.9.0\n")))
(cond2  (#f   (display "cond2.10.2 "))
        (else (display "cond2.10.0 ") (display "cond2.10.1\n")))
(cond2  (#f   (display "cond2.11.3 "))
        (else (display "cond2.11.0 ") (display "cond2.11.1 ") (display "cond2.11.2\n")))





