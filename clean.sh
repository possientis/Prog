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
rm -f c++/a.out
rm -f c++/*.o
rm -f c++/bitcoin/a.out
rm -f c++/bitcoin/*.o
rm -f c/secp256k1/a.out
rm -f c/secp256k1/*.o
rm -f c#/*.exe
rm -f c#/bitcoin/Number/*.dll
rm -f c#/bitcoin/Number/*.exe
rm -f java/*.class
rm -f java/bitcoin/Number/*.class
rm -f java/bitcoin/*.class
rm -f java/universe/*.class
rm -f scala/*.class
rm -f scala/bitcoin/*.class
rm -f clojure/*.class
rm -f clojure/clojure/java/jdbc/*.class
rm -f clojure/rabbitmq/*.class
rm -f clojure/redis/*.class
rm -f clojure/redis/connection/*.class
rm -f clojure/redis/protocol/*.class
rm -f clojure/clojure/java/*.class
rm -f clojure/clojure/contrib/*.class
rm -f clojure/clojure/contrib/io/*.class
rm -f clojure/hiccup/*.class
rm -f clojure/hiccup/util/*.class
rm -f clojure/hiccup/compiler/*.class
rm -f clojure/compojure/*.class
rm -f haskell/*.hi
rm -f haskell/*.o
rm -f haskell/test
rm -f assembly/*.o
rm -f assembly/a.out
rm -f assembly/test.dat
rm -f scala/*.class
rm -f coq/*.glob
rm -f coq/*.vo
rm -fr python/__pycache__
git status


