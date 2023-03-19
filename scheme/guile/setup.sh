#!/bin/sh

root="/home/john/Prog/scheme"

current=$(pwd)

cd /usr/share/guile/2.2/

sudo mkdir -p foo
cd foo
sudo ln -nfs ${root}/guile/bar-module.scm bar-module.scm
cd ..

sudo mkdir -p math
cd math
sudo ln -nfs ${root}/guile/bessel.scm bessel.scm
cd ..

sudo mkdir -p bitcoin
cd bitcoin
sudo ln -nfs ${root}/bitcoin/secp256k1/secp256k1.scm secp256k1.scm

cd /usr/lib/x86_64-linux-gnu/guile/2.2
sudo mkdir -p extensions
cd extensions
sudo ln -nfs /home/john/Prog/scheme/guile/libguile-bessel.so libguile-bessel.so

cd ${current}
