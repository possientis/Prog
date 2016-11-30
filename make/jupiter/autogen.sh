#!/bin/sh

# errors in this script will not be picked up

autoreconf --install
automake --add-missing --copy > /dev/null 2>&1 # partial failure expected
cd .  # artificially restoring $? to 0
