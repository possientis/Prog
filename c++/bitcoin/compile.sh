#!/bin/sh

g++ -L/home/john/Libs/secp256k1/.libs -std=c++14 "$@" $(pkg-config --libs libbitcoin) 


