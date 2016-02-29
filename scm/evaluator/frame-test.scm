(load "dictionary-test.scm")
(dictionary-test "frame1.scm" 'frame1)(newline)
;(dictionary-test "frame2.scm" 'frame2)(newline)
;(dictionary-test "frame3.scm" 'frame3)(newline)
;(dictionary-test "frame4.scm" 'frame4)(newline)
;(dictionary-test "frame.scm" 'frame)  (newline)
(display frame1)(newline) ; global environment polluted
; can we achieve name encapsulation with loads?
(exit 0)


