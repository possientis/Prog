#!/bin/sh
# usage:> ./run.sh file1[.java] file2[.java]

# expecting two arguments
E_WRONG_ARGS=85
if [ $# -ne  2 ]
then
  echo "Usage: ./`basename $0` file1[.java] file2[.java]"
  exit $E_WRONG_ARGS
fi

# retrieving filename (possibly with a .java extension)
FILENAME1=$1
FILENAME2=$2

# removing the .java extension if applicable
echo $FILENAME1 | grep '.java' > /dev/null # > /dev/null to suppress output
if [ $? -eq 0 ]   # grep was successful, need to discard '.java' extension
then
  FILENAME1=`echo $FILENAME1 | grep '.java' | cut -d. -f1`
fi

# removing the .java extension if applicable
echo $FILENAME2 | grep '.java' > /dev/null # > /dev/null to suppress output
if [ $? -eq 0 ]   # grep was successful, need to discard '.java' extension
then
  FILENAME2=`echo $FILENAME2 | grep '.java' | cut -d. -f1`
fi


# setting up various strings
FILENAME_JAR=$FILENAME1.jar
FILENAME_HTML=$FILENAME1.html

# cleaning up previously created files, if any
rm -f $FILENAME1.class # -f to ignore non-existent file
rm -f $FILENAME2.class # -f to ignore non-existent file
rm -f $FILENAME_JAR   # -f to ignore non-existent file
rm -f $FILENAME_HTML  # -f to ignore non-existent file

# compiling source file
javac -classpath acm.jar $FILENAME1.java $FILENAME2.java

# making copy of acm.jar
cp acm.jar $FILENAME_JAR

# adding bytecode files to archive
jar uf $FILENAME_JAR $FILENAME1.class $FILENAME2.class

# creating html file
echo "<html><applet archive=$FILENAME_JAR \
  code=$FILENAME1.class width=1000 height=600></applet></html>" \
  > $FILENAME_HTML

# launching applet
appletviewer $FILENAME_HTML

# final cleanup
rm -f $FILENAME1.class # -f to ignore non-existent file
rm -f $FILENAME2.class # -f to ignore non-existent file
rm -f $FILENAME_JAR   # -f to ignore non-existent file
#rm -f $FILENAME_HTML  # -f to ignore non-existent file

exit

