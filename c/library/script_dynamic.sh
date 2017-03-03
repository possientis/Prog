#!/bin/sh
# Dynamically loaded library demo

if [ ! -f "libhello.so" ]; then
  echo "Please run script_shared.sh before running this script"
  echo "This is to ensure shared library file has been created"
  exit 1
fi

# Presume that libhello.so and friends have
# been created (see dynamic example).
# Compile demo_dynamic program file into an object file.

gcc -Wall -g -c demo_dynamic.c

# Create program demo_use.
# Note that we don’t have to tell it where to search for DL libraries,
# since the only special library this program uses won’t be
# loaded until after the program starts up.
# However, we DO need the option -ldl to include the library
# that loads the DL libraries.

gcc -g -o demo_dynamic demo_dynamic.o -ldl

# Execute the program. Note that we need to tell the
# program where get the dynamically loaded library,
# using LD_LIBRARY_PATH.

LD_LIBRARY_PATH="." ./demo_dynamic
