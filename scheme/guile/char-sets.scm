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



(exit 0)
