#!/bin/sh

rm -f logic/logic.aux
rm -f logic/logic.dvi
rm -f logic/logic.idx
rm -f logic/logic.out
rm -f logic/logic.toc
rm -f logic/logic.pdf
rm -f c/a.out 
rm -f c/*.o
rm -f c/tlpi/a.out
rm -f c/tlpi/*.o
rm -f cpp/a.out
rm -f cpp/*.o
rm -f c#/*.exe
rm -f java/*.class
rm -f scala/*.class
rm -f clojure/*.class
rm -f clojure/clj_record/*.class
rm -f clojure/clojure/java/*.class
rm -r clojure/clojure/java/jdbc
rm -f haskell/*.hi
rm -f haskell/*.o
rm -f haskell/test
rm -f asm/*.o
rm -f asm/a.out
rm -f asm/test.dat
rm -f scala/*.class
rm -f coq/*.glob
rm -f coq/*.vo
git status


