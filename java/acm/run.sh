#!/bin/sh
# usage:> ./run.sh filename[.java]

# expecting a single argument
E_WRONG_ARGS=85
if [ $# -ne  1 ]
then
  echo "Usage: ./`basename $0` filename[.java]"
  exit $E_WRONG_ARGS
fi

# retrieving filename (possibly with a .java extension)
FILENAME=$1

# removing the .java extension if applicable
echo $FILENAME | grep '.java' > /dev/null # > /dev/null to suppress output
if [ $? -eq 0 ]   # grep was successful, need to discard '.java' extension
then
  FILENAME=`echo $FILENAME | grep '.java' | cut -d. -f1`
fi

# setting up various strings
FILENAME_CLASS=$FILENAME.class
FILENAME_JAR=$FILENAME.jar
FILENAME_HTML=$FILENAME.html
FILENAME_JAVA=$FILENAME.java

# cleaning up previously created files, if any
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

