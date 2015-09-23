#!/usr/bin/scm
; usage:> ./run.scm filename[.java]
; not portable to mit-scheme (*argv* is unbound)

; wrapper around execl to execute linux command 'rm -f filename'
(define (cleanUpFile filename)
  (let ((pid (fork)))
    (if (= 0 pid)
      (begin  ; child process
        (execl "/bin/rm" "/bin/rm" "-f" filename)
        (exit 1)) ; does not return from execve unless failure
      (begin ; parent process
        (let ((status (waitpid pid 0))) ; waiting for child to complete
          (if (not (= 0 status))        ; child failed
            (begin
              (display "Failed to remove ")
              (display filename)
              (newline)
              (exit 1))))))))

; wrapper around execl to execute command 'javac -classpath acm.jar filename'
(define (compileFile filename)
  (let ((pid (fork)))
    (if (= 0 pid)
      (begin  ; child process
        (execl "/usr/bin/javac" "/usr/bin/javac" "-classpath" "acm.jar" filename)
        (exit 1)) ; does not return from execve unless failure
      (begin ; parent process
        (let ((status (waitpid pid 0))) ; waiting for child to complete
          (if (not (= 0 status))        ; child failed
            (begin
              (display "Failed to compile ")
              (display filename)
              (newline)
              (exit 1))))))))


; wrapper around execl to execute command 'cp acm.jar filename.jar'
(define (copyAcmAsFile filename)
  (let ((pid (fork)))
    (if (= 0 pid)
      (begin  ; child process
        (execl "/bin/cp" "/bin/cp" "acm.jar" filename)
        (exit 1)) ; does not return from execve unless failure
      (begin ; parent process
        (let ((status (waitpid pid 0))) ; waiting for child to complete
          (if (not (= 0 status))        ; child failed
            (begin
              (display "Failed to copy acm.jar as ")
              (display filename)
              (newline)
              (exit 1))))))))


; wrapper around execl to execute command 'jar uf filename.jar filename.class'
(define (addToJarFile filename-jar filename-class)
  (let ((pid (fork)))
    (if (= 0 pid)
      (begin  ; child process
        (execl "/usr/bin/jar" "/user/bin/jar" "uf" filename-jar filename-class)
        (exit 1)) ; does not return from execve unless failure
      (begin ; parent process
        (let ((status (waitpid pid 0))) ; waiting for child to complete
          (if (not (= 0 status))        ; child failed
            (begin
              (display "Failed to add ")
              (display filename-class)
              (display " to ")
              (display filename-jar)
              (newline)
              (exit 1))))))))


; wrapper around execl to execute linux command 'appletviewer filename.html'
(define (launchApplet filename)
  (let ((pid (fork)))
    (if (= 0 pid)
      (begin  ; child process
        (execl "/usr/bin/appletviewer" "/usr/bin/appletviewer" filename)
        (exit 1)) ; does not return from execve unless failure
      (begin ; parent process
        (let ((status (waitpid pid 0))) ; waiting for child to complete
          (if (not (= 0 status))        ; child failed
            (begin
              (display "Failed to launch applet ")
              (display filename)
              (newline)
              (exit 1))))))))



(define arguments (program-arguments))
; expecting a single argument
(if (not (= 3 (length arguments)))
  (begin
    (display "Usage:")
    (display (cadr arguments)) ; ./run.scm (or whatever filename it is)
    (display " filename[.java]\n")
    (exit 0)))

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
(cleanUpFile filename-class)
(cleanUpFile filename-jar)
(cleanUpFile filename-html)

; compiling filename.java
(compileFile filename-java)

; copying acm.jar as filename.jar
;(copy-file "acm.jar" filename-jar) -> should work, need to link something
(copyAcmAsFile filename-jar)

; adding filename.class to filename.jar
(addToJarFile filename-jar filename-class)

; creating html file
(define file (open-file filename-html open_write))
(display "<html><applet archive=" file)
(display filename-jar file)
(display " code=" file)
(display filename-class file)
(display " width=1000 height=600></applet></html>" file)
(close-port file)

; launching applet
(launchApplet filename-html)

; final clean-up
(cleanUpFile filename-class)
(cleanUpFile filename-jar)
(cleanUpFile filename-html)

(exit 0)
