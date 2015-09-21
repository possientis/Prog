#!/bin/sh
# usage:> ./run.sh filename[.java]

# expecting a single argument
E_WRONG_ARGS=85
if [ $# -ne  1 ]
then
  echo "Usage: `basename $0` filename"
  exit $E_WRONG_ARGS
fi

FILENAME=$1   # no space around '='

FILENAME_CLASS=$FILENAME.class
FILENAME_JAR=$FILENAME.jar
FILENAME_HTML=$FILENAME.html
FILENAME_JAVA=$FILENAME.java

# cleaning previously created files, if any
rm -f $FILENAME_CLASS # -f to ignore non-existent file
rm -f $FILENAME_JAR   # -f to ignore non-existent file
rm -f $FILENAME_HTML  # -f to ignore non-existent file

# compiling source file
javac -classpath acm.jar $FILENAME_JAVA

# making copy of acm.jar
cp acm.jar $FILENAME_JAR

# adding bytecode file to archive
jar uf $FILENAME_JAR $FILENAME_CLASS

# creating html file
echo "<html><applet archive=$FILENAME_JAR \
  code=$FILENAME_CLASS width=1000 height=600></applet></html>" \
  > $FILENAME_HTML

# launching applet
appletviewer $FILENAME_HTML

# final cleanup
rm -f $FILENAME_CLASS # -f to ignore non-existent file
rm -f $FILENAME_JAR   # -f to ignore non-existent file
rm -f $FILENAME_HTML  # -f to ignore non-existent file

exit

