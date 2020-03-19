#!/bin/bash

ldd --version | head -n1 | cut -d" " -f2- #glibc version
