#!/bin/bash

echo -n "Binutils: "; ld --version | head -n1 | cut -d" " -f3-
