(define (assert condition message)
  (if condition 'done (error message)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                                  0                                   ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define nul #\nul)
(assert (char=? nul #\nul)    "nul.0")
(assert (char=? nul #\000)    "nul.1")
(assert (char=? nul #\x0000)  "nul.2")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                                  1                                   ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define soh #\soh)
(assert (char=? soh #\soh)    "soh.0")
(assert (char=? soh #\001)    "soh.1")
(assert (char=? soh #\x0001)  "soh.2")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                                  2                                   ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define stx #\stx)
(assert (char=? stx #\stx)    "stx.0")
(assert (char=? stx #\002)    "stx.1")
(assert (char=? stx #\x0002)  "stx.2")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                                  3                                   ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define etx #\etx)
(assert (char=? etx #\etx)    "etx.0")
(assert (char=? etx #\003)    "etx.1")
(assert (char=? etx #\x0003)  "etx.2")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                                  4                                   ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define eot #\eot)
(assert (char=? eot #\eot)    "eot.0")
(assert (char=? eot #\004)    "eot.1")
(assert (char=? eot #\x0004)  "eot.2")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                                  5                                   ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define enq #\enq)
(assert (char=? enq #\enq)    "enq.0")
(assert (char=? enq #\005)    "enq.1")
(assert (char=? enq #\x0005)  "enq.2")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                                  6                                   ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define ack #\ack)
(assert (char=? ack #\ack)    "ack.0")
(assert (char=? ack #\006)    "ack.1")
(assert (char=? ack #\x0006)  "ack.2")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                                  7                                   ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define alarm #\alarm)
(assert (char=? alarm #\alarm)  "alarm.0")
(assert (char=? alarm #\bel)    "alarm.1")
(assert (char=? alarm #\007)    "alarm.2")
(assert (char=? alarm #\x0007)  "alarm.3")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                                  8                                   ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define backspace #\backspace)
(assert (char=? backspace #\backspace)  "backspace.0")
(assert (char=? backspace #\bs)         "backspace.1")
(assert (char=? backspace #\010)        "backspace.2")
(assert (char=? backspace #\x0008)      "backspace.3")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                                  9                                   ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define tab #\tab)
(assert (char=? tab #\tab)    "tab.0")
(assert (char=? tab #\ht)     "tab.1")
(assert (char=? tab #\011)    "tab.2")
(assert (char=? tab #\x0009)  "tab.3")


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                                 10                                   ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define linefeed #\linefeed)
(assert (char=? linefeed #\linefeed)  "linefeed.0")
(assert (char=? linefeed #\lf)        "linefeed.1")
(assert (char=? linefeed #\newline)   "linefeed.2")
(assert (char=? linefeed #\012)       "linefeed.3")
(assert (char=? linefeed #\x000a)     "linefeed.4")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                                 11                                   ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define vtab #\vtab)
(assert (char=? vtab #\vtab)   "vtab.0")
(assert (char=? vtab #\vt)     "vtab.1")
(assert (char=? vtab #\013)    "vtab.2")
(assert (char=? vtab #\x000b)  "vtab.3")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                                 12                                   ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define page #\page)
(assert (char=? page #\page)   "page.0")
(assert (char=? page #\ff)     "page.1")
(assert (char=? page #\014)    "page.2")
(assert (char=? page #\x000c)  "page.3")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                                 13                                   ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define return #\return)
(assert (char=? return #\return) "return.0")
(assert (char=? return #\cr)     "return.1")
(assert (char=? return #\015)    "return.2")
(assert (char=? return #\x000d)  "return.3")

; TODO

(define esc #\esc)
(assert (char=? esc #\esc)    "esc.0")
(assert (char=? esc #\033)    "esc.1")
(assert (char=? esc #\x001b)  "esc.2")

(define space #\space)
(assert (char=? space #\space)  "space.0")
(assert (char=? space #\040)    "space.1")
(assert (char=? space #\x0020)  "space.2")


(define delete #\delete)
(assert (char=? delete #\delete) "delete.0")
(assert (char=? delete #\177)    "delete.1")
(assert (char=? delete #\x007f)  "delete.2")








(exit 0)
