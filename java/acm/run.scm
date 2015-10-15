#!/usr/bin/scm
; usage:> ./run.scm filename[.java]
; not portable to mit-scheme (*argv* is unbound)

(define arguments (program-arguments))
(display arguments)(newline)
; expecting a single argument
(if (not (= 3 (length arguments)))
  (begin
    (display "Usage:")
    (display (cadr arguments)) ; ./run.scm (or whatever filename it is)
    (display " filename[.java]\n")
    (exit 1)))

; retrieving filename (possibly with a .java extension)
(define filename (caddr arguments)) ; car of cdr of cdr

; removing the .java extension if applicable
(let ((len (string-length filename)))
  (if (> len 5)   ; no ".java" extension otherwise
    (let ((last5char (substring filename (- len 5) len)))
      (if (string=? last5char ".java")
        (let ((new-name (substring filename 0 (- len 5))))
          (set! filename new-name))))))

; setting up various strings
(define filename-class (string-append filename ".class"))
(define filename-jar (string-append filename ".jar"))
(define filename-html (string-append filename ".html"))
(define filename-java (string-append filename ".java"))

; cleaning up previously created files, if any
(system (string-append "rm -f " filename-class))
(system (string-append "rm -f " filename-jar))
(system (string-append "rm -f " filename-html))

; compiling filename.java
(system (string-append "javac -classpath acm.jar " filename-java))

; copying acm.jar as filename.jar
(system (string-append "cp acm.jar " filename-jar))

; adding filename.class to filename.jar
(system (string-append "jar uf " filename-jar " " filename-class))

; creating html file
(define file (open-file filename-html open_write))
(display "<html><applet archive=" file)
(display filename-jar file)
(display " code=" file)
(display filename-class file)
(display " width=1000 height=600></applet></html>" file)
(close-port file)

; launching applet
(system (string-append "appletviewer " filename-html))

; final clean-up
(system (string-append "rm -f " filename-class))
(system (string-append "rm -f " filename-jar))
(system (string-append "rm -f " filename-html))

(exit 0)
