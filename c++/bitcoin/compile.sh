#!/bin/sh

g++ -L${HOME}/Libs/secp256k1/.libs -std=c++14 "$@" $(pkg-config --libs libbitcoin) 


