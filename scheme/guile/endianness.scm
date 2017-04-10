(use-modules (rnrs bytevectors))

(display (native-endianness))(newline)  ; little


(display (eq? (native-endianness) (endianness little)))(newline)  ; #t
(display (eq? (native-endianness) 'little))(newline)              ; #t
