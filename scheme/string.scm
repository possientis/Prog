(define s "He did type \"\\Hello\" in the end\n")
(define h (string-hash s))
(display (number->string h 16))
(newline)
