(use-modules (ice-9 iconv))

(define bytes (string->bytevector "abcdefABCDEF" "utf-8"))

(display bytes)(newline)
