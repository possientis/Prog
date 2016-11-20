#!/bin/sh

# stop on failure
set -e

# setting up build directories
mkdir -p build/org/artima/greeter
mkdir -p build/greeters

# compiling while suppressing deprecation warnings
javac Greet.java -d build
javac greeters/*.java -d build/greeters

# javac producing redundant files (probably not calling it properly)
rm -f build/greeters/org/ -r

# creating run file
echo '#!/bin/sh' > build/run.sh

echo 'java Greet greeters Hello Greetings Salutations HowDoYouDo HiTime'\
      >> build/run.sh

chmod +x build/run.sh

