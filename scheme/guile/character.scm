(define (assert condition message)
  (if condition 'done (error message)))

(define nul #\nul)
(assert (char=? nul #\000)    "nul.1")
(assert (char=? nul #\x0000)  "nul.2")
(assert (eq?    nul #\000)    "nul.3")
(assert (eq?    nul #\x0000)  "nul.4")

(define alarm #\alarm)
(assert (char=? alarm #\007)    "alarm.1")
(assert (char=? alarm #\x0007)  "alarm.2")
(assert (eq?    alarm #\007)    "alarm.3")
(assert (eq?    alarm #\x0007)  "alarm.4")

(define backspace #\backspace)
(assert (char=? backspace #\010)    "backspace.1")
(assert (char=? backspace #\x0008)  "backspace.2")
(assert (eq?    backspace #\010)    "backspace.3")
(assert (eq?    backspace #\x0008)  "backspace.4")

(define tab #\tab)
(assert (char=? tab #\011)    "tab.1")
(assert (char=? tab #\x0009)  "tab.2")
(assert (eq?    tab #\011)    "tab.3")
(assert (eq?    tab #\x0009)  "tab.4")


(define linefeed #\linefeed)
(assert (char=? linefeed #\newline) "linefeed.2")
(assert (char=? linefeed #\012)     "linefeed.1")
(assert (char=? linefeed #\x000a)   "linefeed.2")
(assert (eq?    linefeed #\012)     "linefeed.3")
(assert (eq?    linefeed #\x000a)   "linefeed.4")









(exit 0)
