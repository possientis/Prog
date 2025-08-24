#!/bin/sh

DIR=$(pwd)

cd ${HOME}/Prog/dot
sudo cp agda.vim /usr/share/vim/vim91/syntax
sudo cp coq.vim /usr/share/vim/vim91/syntax
sudo cp haskell.vim /usr/share/vim/vim91/syntax
sudo cp idris.vim /usr/share/vim/vim91/syntax
sudo cp lean.vim /usr/share/vim/vim91/syntax
sudo cp scheme.vim /usr/share/vim/vim91/syntax
sudo cp solarized.vim /usr/share/vim/vim91/colors

cp .bash_aliases ${HOME}/
cp .dircolors ${HOME}/
cp .gdbinit ${HOME}/
cp .guile ${HOME}/
cp .vimrc ${HOME}/

mkdir -p ${HOME}/.gradle
cp gradle.properties ${HOME}/.gradle

cd $DIR
