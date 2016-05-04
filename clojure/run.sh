#!/bin/sh

# ACTUALLY, SEEMS THIS WRONG...

# running clojure program using a local version of clojure.jar
# this can only work if depencies to clojure.jar can be found.
# These dependencies can be found in the META-INF/MANIFEST.MF
# file obtained when you unzip clojure-1.6.0.jar.
# Hence these dependencies appear as symbolic link in our
# working directory:

# replaced by local clojure.jar, so here for reference but not needed
# lrwxrwxrwx 1 john john      33 Apr 30 11:20 clojure-1.6.0.jar -> /usr/share/java/clojure-1.6.0.jar

# dependencies

# lrwxrwxrwx 1 john john      32 May  4 10:59 asm4-commons.jar  -> /usr/share/java/asm4-commons.jar
# lrwxrwxrwx 1 john john      24 May  4 10:55 asm4.jar          -> /usr/share/java/asm4.jar
# lrwxrwxrwx 1 john john      27 May  4 11:01 jsr166y.jar       -> /usr/share/java/jsr166y.jar

java -cp .:./clojure.jar $1 $2 $3 $4 $5 $6




