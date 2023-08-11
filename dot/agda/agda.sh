#!/bin/sh

DIR=$(pwd)

cd ${HOME}/Prog/dot/agda

mkdir -p ${HOME}/.agda
mkdir -p ${HOME}/Libs/agda
mkdir -p ${HOME}/Libs/agda/src

cp libraries ${HOME}/.agda
cp defaults ${HOME}/.agda
cp standard-library.agda-lib ${HOME}/Libs/agda

rsync -av /usr/share/agda-stdlib/ ${HOME}/Libs/agda/src/

cd $DIR
