; example of code using 'execl' and 'fork'
; made unnecessary by the existence of 'system'

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



