#!/bin/sh

# MESSING AROUND WITH JAVA ARCHIVES

# This is a good learning exercise, but will probably fail as 
# soon as code requires external java dependencies, i.e. dependencies
# which are not within the clojure jar (and it dependencies)

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

# Furthermore, it is importance that the local archive clojure.jar is created with the correct 
# manifest. For example, start with clojure-1.6.0.jar

# jar -xf clojure-1.6.0.jar     # extracting archive, creates directories 'clojure' and 'META-INF'

# then add the correct source .clj file in the correct location
# for example, jdbc.clj (which declares the namespace 'clojure.java.jdbc' should be located in 
# clojure/java. Once the source file is copied into its correct location, compile it from the
# working directory as:

# clojurec clojure.java.jdbc    # will generate all the .class files in the correct place

# then you are ready to create a new customized archive clojure.jar but don't forget to 
# pass in the original manifest file

# c='compress', m=manifest (1st argument), f=jar filename
# jar cmf META-INF/MANIFEST.MF clojure.jar clojure        # clojure.jar created


# local customized jar (need to be properly created , see above)
#java -cp .:./clojure.jar $1 $2 $3 $4 $5 $6

# This is all very nice, but totally unnecessary. In order to add functionality to clojure,
# there is no need to manufacture a new archive. Just create clojure/java/ with jdbc.clj 
# from the working directory, and you can just used the standard jar with '.'
# standard jar (via local symlink)

java -cp .:/usr/share/java/clojure-1.6.0.jar $1 $2 $3 $4 $5 $6





