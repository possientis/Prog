(define set (char-set #\a #\b #\c #\d #\e))
(define other (char-set #\a))

(display (char-set? set))(newline)        ; #t
(display (char-set= set set))(newline)    ; #t
(display (char-set= set other))(newline)  ; #f
(display (char-set<= set other))(newline) ; #f
(display (char-set<= other set))(newline) ; #t
(display (char-set-hash set))(newline)    ; 420
(display (char-set-hash other))(newline)  ; 97

(define iter (char-set-cursor set))

(define (char-set-for-each proc cs)
  (display "for-each is running ...\n")
  (if (not (char-set? cs)) 
    (error "char-set-for-each: set argument should be a character set"))
  (let loop ((cursor (char-set-cursor cs)))
    (if (end-of-char-set? cursor)
      'done
      (begin
        (proc (char-set-ref cs cursor))
        (loop (char-set-cursor-next cs cursor))))))


(define new char-set:symbol)


(display (string-append "abc" "def" "hij"))(newline)


(exit 0)
