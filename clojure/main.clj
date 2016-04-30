; you need to define a namespace using the 'ns' macro 
; and it needs to match the filename. The namespace need 
; not be 'main' of course (we decided to call our file 
; main.clj, that's all ...).

(ns main (:gen-class))

; the :gen-class directive will ensure that main.class is created
; when the file is compiled. This will allow us to launch the 
; program with the 'java' command, as in:

;  java main                # hhmm, actually life is not that simple :(

; However, the truth is more complicated. First of all, the main.class
; file will not be useful unless main.clj contains an entry
; point in the form of (defn -main [& arg]) (see below).

; '[& arg]' for optional arguments, but [arg] [arg1 arg2] etc also fine
; note that clojure expects entry point to be called '-main'
(defn -main [& arg] 
  (println "running with arg =" (str arg)))

; secondly, this class file has dependencies to clojure, so 
; unless you tell java where to get the appropriate libraries,
; it will fail to run.

; 'cp' stands for class-path
; java -cp /usr/share/java/clojure-1.6.0.jar main       # better

; unfortunately, this will not work either, as java will not look 
; into the current directory for the file main.class as soon as 
; you use the -cp option. So you need to add the current directory '.' 
; to the class-path specification

; can you see the '.' ?
; java -cp .:/usr/shara/java/clojure-1.6.0.jar main --> should work now

; In order to compile main.clj:

; clojurec main                 # for once, simplicity has it

; this will have the effect of creating all the *.class bytecode files
; into the current directory. If you want to avoid this mess, you can
; create a directory (say 'class')

; mkdir class

; and then specify this directory as the destination of compilation:

; clojurec -d class main        # nah, too simple

; if you use the -d directive, then clojurec will no longer find main.clj
; in the current directory (a bit like the 'java' command)

; clojurec -d class -cp . main  # this should work now

; However, note that main.class is now in ./class and not in ./, hence

; # 'main' refers to namespace, not the file, so don't try to use 'class/main'
; java -cp ./class:/usr/share/java/clojure-1.6.0.jar main  

; for example
; java -cp ./class:/usr/share/java/clojure-1.6.0.jar main  a b c d 

; OUTPUT:
; running with arg = ("a" "b" "c" "d")






