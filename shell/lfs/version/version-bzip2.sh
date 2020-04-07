#!/bin/bash

bzip2 --version 2>&1 < /dev/null | head -n1 | cut -d" " -f1,6-
