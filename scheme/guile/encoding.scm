(use-modules (ice-9 iconv))

(define bytes (string->bytevector "abcdefABCDEF" "utf-8"))

(display bytes)(newline)

(set! bytes #vu8(0 61 32))  ; bytevector literal

(display bytes)(newline)

(display (string-bytes-per-char "abcdefABCDEF"))(newline)

(display (%string-dump "abcdefABCDEF"))(newline)
