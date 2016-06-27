#!/bin/sh
HICCUP_JARS=
for d in `dirname $0`/*.jar
do
    HICCUP_JARS="$d:$HICCUP_JARS"
done

# comment out when happy
# echo $HICCUP_JARS

# compiling while suppressing stdout comment
clojurec -cp "$HICCUP_JARS" "$@" 1> /dev/null

# running program
java -cp "$HICCUP_JARS" "$@"

# clean up
rm *.class; 

# clean up library
rm hiccup/*.class; rm hiccup/compiler/*.class; rm hiccup/util/*.class


