#!/bin/sh

# Creates dependency files needed for inclusion in Makefile

DIR=$(pwd)

# Temporary files are created on the /tmp directory to avoid race
# condition with the 'grep -r'

# Processing 'Require Import'
grep 'Require Import Logic\.' -r | cat - > /tmp/deps
sed -i 's/\.v\:Require Import Logic\./.vo:/g' /tmp/deps
sed -i 's/\.vo\:\([[:alnum:]]*\)\.\([[:alnum:]]*\)\.\([[:alnum:]]*\)\./.vo : \1\/\2\/\3.vo/g' /tmp/deps
sed -i 's/\.vo\:\([[:alnum:]]*\)\.\([[:alnum:]]*\)\./.vo : \1\/\2.vo/g' /tmp/deps

# Ssimilar process for dependencies without 'Import', just 'Require'
grep 'Require[[:space:]]*Logic\.' -r | cat - > /tmp/deps_
sed -i 's/\.v\:Require[[:space:]]*Logic\./.vo:/g' /tmp/deps_
sed -i 's/\.vo\:\([[:alnum:]]*\)\.\([[:alnum:]]*\)\.\([[:alnum:]]*\)\./.vo : \1\/\2\/\3.vo/g' /tmp/deps_
sed -i 's/\.vo\:\([[:alnum:]]*\)\.\([[:alnum:]]*\)\./.vo : \1\/\2.vo/g' /tmp/deps_

cat /tmp/deps_ >> /tmp/deps
mv /tmp/deps ${DIR}/deps
rm -f /tmp/deps /tmp/deps_
