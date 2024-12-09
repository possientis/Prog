#!/bin/sh

# Creates dependency files needed for inclusion in Makefile

DIR=$(pwd)

# Temporary files are created on the /tmp directory to avoid race
# condition with the 'grep -r'

# Processing 'Require Import'
grep 'Require Import ZF\.' -r > /tmp/depsZF
sed -i 's/\.v\:Require Import ZF\./.vo:/g' /tmp/depsZF
sed -i 's/\.vo\:\([[:alnum:]]*\)\.\([[:alnum:]]*\)\.\([[:alnum:]]*\)\./.vo : \1\/\2\/\3.vo/g' /tmp/depsZF
sed -i 's/\.vo\:\([[:alnum:]]*\)\.\([[:alnum:]]*\)\./.vo : \1\/\2.vo/g' /tmp/depsZF
sed -i 's/\.vo\:\([[:alnum:]]*\)\./.vo : \1.vo/g' /tmp/depsZF

# Ssimilar process for dependencies without 'Import', just 'Require'
grep 'Require[[:space:]]*ZF\.' -r > /tmp/depsZF_
sed -i 's/\.v\:Require[[:space:]]*ZF\./.vo:/g' /tmp/depsZF_
sed -i 's/\.vo\:\([[:alnum:]]*\)\.\([[:alnum:]]*\)\.\([[:alnum:]]*\)\./.vo : \1\/\2\/\3.vo/g' /tmp/depsZF_
sed -i 's/\.vo\:\([[:alnum:]]*\)\.\([[:alnum:]]*\)\./.vo : \1\/\2.vo/g' /tmp/depsZF_
sed -i 's/\.vo\:\([[:alnum:]]*\)\./.vo : \1.vo/g' /tmp/depsZF_

cat /tmp/depsZF_ >> /tmp/depsZF
mv /tmp/depsZF ${DIR}/deps
rm -f /tmp/depsZF /tmp/depsZF_
