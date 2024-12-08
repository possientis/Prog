#!/bin/sh

# Creates dependency files needed for inclusion in Makefile

DIR=$(pwd)

# Temporary files are created on the /tmp directory to avoid race
# condition with the 'grep -r'

# Processing 'Require Import'
grep 'Require Import Logic\.' -r > /tmp/depsLogic
sed -i 's/\.v\:Require Import Logic\./.vo:/g' /tmp/depsLogic
sed -i 's/\.vo\:\([[:alnum:]]*\)\.\([[:alnum:]]*\)\.\([[:alnum:]]*\)\./.vo : \1\/\2\/\3.vo/g' /tmp/depsLogic
sed -i 's/\.vo\:\([[:alnum:]]*\)\.\([[:alnum:]]*\)\./.vo : \1\/\2.vo/g' /tmp/depsLogic

# Ssimilar process for dependencies without 'Import', just 'Require'
grep 'Require[[:space:]]*Logic\.' -r > /tmp/depsLogic_
sed -i 's/\.v\:Require[[:space:]]*Logic\./.vo:/g' /tmp/depsLogic_
sed -i 's/\.vo\:\([[:alnum:]]*\)\.\([[:alnum:]]*\)\.\([[:alnum:]]*\)\./.vo : \1\/\2\/\3.vo/g' /tmp/depsLogic_
sed -i 's/\.vo\:\([[:alnum:]]*\)\.\([[:alnum:]]*\)\./.vo : \1\/\2.vo/g' /tmp/depsLogic_

cat /tmp/depsLogic_ >> /tmp/depsLogic
mv /tmp/depsLogic ${DIR}/deps
rm -f /tmp/depsLogic /tmp/depsLogic_
