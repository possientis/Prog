#!/bin/sh

DIR="${HOME}/Prog/scheme"

cd /usr/share/guile/2.2/

sudo mkdir -p foo
cd foo
sudo ln -nfs ${DIR}/guile/bar-module.scm bar-module.scm
cd ..

sudo mkdir -p math
cd math
sudo ln -nfs ${DIR}/guile/bessel.scm bessel.scm
cd ..

sudo mkdir -p bitcoin
cd bitcoin
sudo ln -nfs ${DIR}/bitcoin/secp256k1/secp256k1.scm secp256k1.scm

cd /usr/lib/x86_64-linux-gnu/guile/2.2
sudo mkdir -p extensions
cd extensions
sudo ln -nfs ${DIR}/guile/libguile-bessel.so libguile-bessel.so
