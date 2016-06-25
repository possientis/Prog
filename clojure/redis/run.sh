#!/bin/sh
REDIS_JARS=
for d in `dirname $0`/*.jar
do
    REDIS_JARS="$d:$REDIS_JARS"
done

# echo $REDIS_JARS

# compiling while suppressing stdout comment
clojurec -cp "$REDIS_JARS" "$@" 1> /dev/null

# running program
java -cp "$REDIS_JARS" "$@"

# clean up
rm *.class; 

# comment out these lines to avoid recompiling library each time
rm redis/*.class; rm redis/channel/*.class
rm redis/connection/*.class; rm redis/connection_pool/*.class
rm redis/protocol/*.class

