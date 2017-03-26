#!/bin/sh

g++ -std=c++14 "$@" $(pkg-config --libs libbitcoin) 


